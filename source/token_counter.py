#!/usr/bin/env python3
import argparse
import json
import os
import re
import sys
from typing import List, Tuple, Optional, Any

try:
    import tiktoken
except ImportError:
    print("Please install tiktoken: pip install tiktoken", file=sys.stderr)
    sys.exit(1)

THINK_RE = re.compile(r"<think>(.*?)</think>", re.DOTALL | re.IGNORECASE)

def extract_assistant_think_texts(conversation_path: str) -> List[str]:
    """Return all text inside <think>...</think> from assistant messages only."""
    try:
        with open(conversation_path, "r", encoding="utf-8") as f:
            conv = json.load(f)
    except Exception as e:
        print(f"ERROR reading {conversation_path}: {e}", file=sys.stderr)
        return []

    texts: List[str] = []
    if isinstance(conv, list):
        for msg in conv:
            try:
                if isinstance(msg, dict) and msg.get("role") == "assistant":
                    content = msg.get("content", "")
                    if isinstance(content, str):
                        texts.extend(THINK_RE.findall(content))
            except Exception:
                continue
    return texts

def count_tokens(texts: List[str], encoding_name: str) -> int:
    if not texts:
        return 0
    try:
        try:
            enc = tiktoken.encoding_for_model(encoding_name)
        except KeyError:
            enc = tiktoken.get_encoding("cl100k_base")
        total = 0
        for t in texts:
            total += len(enc.encode(t))
        return total
    except Exception as e:
        print(f"ERROR tokenizing: {e}", file=sys.stderr)
        return 0

def insert_after_pass_number(orig: dict, key: str, value) -> dict:
    """
    Return a new dict with (key, value) inserted right after 'pass_number'.
    If 'reasoning_token_count' already exists, it will be updated and kept
    right after 'pass_number'. If 'pass_number' is not present, append at end.
    """
    newd = {}
    inserted = False
    for k, v in orig.items():
        newd[k] = v
        if k == "pass_number":
            newd[key] = value
            inserted = True
    if not inserted:
        newd[key] = value
    return newd

def update_evaluation_with_count(eval_path: str, count: int) -> bool:
    """Insert or update reasoning_token_count under pass_number. Returns True on success."""
    try:
        with open(eval_path, "r", encoding="utf-8") as f:
            data = json.load(f)
    except Exception as e:
        print(f"ERROR reading {eval_path}: {e}", file=sys.stderr)
        return False

    if not isinstance(data, dict):
        print(f"WARNING: {eval_path} is not a JSON object; skipping update.", file=sys.stderr)
        return False

    data = insert_after_pass_number(data, "reasoning_token_count", int(count))

    try:
        with open(eval_path, "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False, indent=4)
            f.write("\n")
        return True
    except Exception as e:
        print(f"ERROR writing {eval_path}: {e}", file=sys.stderr)
        return False

def has_required_files(folder: str) -> bool:
    return (
        os.path.isfile(os.path.join(folder, "conversation.json")) and
        os.path.isfile(os.path.join(folder, "evaluation.json"))
    )

def _safe_int(value: Any) -> Optional[int]:
    try:
        if value is None:
            return None
        if isinstance(value, (int, float)):
            return int(value)
        if isinstance(value, str) and value.strip():
            return int(float(value))
    except Exception:
        return None
    return None

def get_existing_reasoning_tokens(eval_path: str) -> Optional[int]:
    """
    Return existing reasoning token count from evaluation.json if present.
    Checks:
      - top-level 'reasoning_token_count'
      - 'timing.reasoning_tokens'
    """
    try:
        with open(eval_path, "r", encoding="utf-8") as f:
            data = json.load(f)
    except Exception as e:
        print(f"ERROR reading {eval_path}: {e}", file=sys.stderr)
        return None

    if not isinstance(data, dict):
        return None

    # Prefer explicit top-level count if present and nonzero
    top = _safe_int(data.get("reasoning_token_count"))
    if top is not None and top > 0:
        return top

    # Otherwise look under timing.reasoning_tokens
    timing = data.get("timing")
    if isinstance(timing, dict):
        rt = _safe_int(timing.get("reasoning_tokens"))
        if rt is not None and rt >= 0:
            return rt

    return None

def discover_candidates(root: str, strict_children_only: bool) -> List[str]:
    candidates: List[str] = []

    # If root itself is a 1_pass folder with the files, allow processing it directly.
    if os.path.basename(os.path.normpath(root)) == "1_pass" and has_required_files(root):
        candidates.append(root)

    if strict_children_only:
        for d in os.listdir(root):
            path = os.path.join(root, d)
            if os.path.isdir(path):
                # Only accept immediate children that are exactly 1_pass
                if os.path.basename(path) == "1_pass" and has_required_files(path):
                    candidates.append(path)
    else:
        for dirpath, dirnames, filenames in os.walk(root):
            # Filter to only directories named 1_pass
            if os.path.basename(dirpath) != "1_pass":
                continue
            if "conversation.json" in filenames and "evaluation.json" in filenames:
                candidates.append(dirpath)

    return sorted(set(candidates))

def process_root(root: str, encoding_name: str, strict_children_only: bool) -> Tuple[int, int]:
    """
    Walk the root directory and process only folders named '1_pass' that
    contain both conversation.json and evaluation.json.

    Returns (folders_processed, total_tokens).
    """
    folders_processed = 0
    total_tokens = 0

    candidates = discover_candidates(root, strict_children_only)

    # 1) First pass: try to use existing counts if any are present
    existing_counts: List[Tuple[str, int]] = []
    for folder in candidates:
        evaluation_path = os.path.join(folder, "evaluation.json")
        existing = get_existing_reasoning_tokens(evaluation_path)
        if existing is not None:
            existing_counts.append((folder, existing))

    if existing_counts:
        # Report and average existing counts, skip extraction entirely
        for folder, cnt in existing_counts:
            print(f"{os.path.basename(folder)}\t{cnt}")
            folders_processed += 1
            total_tokens += cnt

        avg = total_tokens / folders_processed if folders_processed else 0.0
        print(f"\nAVERAGE_TOKENS_PER_RESPONSE\t{avg:.2f}")
        return folders_processed, total_tokens

    # 2) If no existing counts found, fall back to extraction
    for folder in candidates:
        conversation_path = os.path.join(folder, "conversation.json")
        evaluation_path = os.path.join(folder, "evaluation.json")

        think_texts = extract_assistant_think_texts(conversation_path)
        token_count = count_tokens(think_texts, encoding_name)

        # Progress line: "folder_name<TAB>count"
        print(f"{os.path.basename(folder)}\t{token_count}")

        update_evaluation_with_count(evaluation_path, token_count)

        folders_processed += 1
        total_tokens += token_count

    return folders_processed, total_tokens

def main():
    parser = argparse.ArgumentParser(
        description="Count assistant <think> tokens for 1_pass folders and annotate evaluation.json. "
                    "If existing reasoning token counts are present, average those and skip extraction."
    )
    parser.add_argument("root", help="Path to the root folder (e.g., ./.../n_pass_noconfeed).")
    parser.add_argument(
        "--model",
        default="gpt-4o-mini",
        help="Model name for tiktoken encoding (default: gpt-4o-mini). Falls back to cl100k_base if unknown.",
    )
    parser.add_argument(
        "--recursive",
        action="store_true",
        help="Recursively find 1_pass subfolders that contain conversation.json and evaluation.json.",
    )
    args = parser.parse_args()

    if not os.path.isdir(args.root):
        print(f"ERROR: '{args.root}' is not a directory.", file=sys.stderr)
        sys.exit(1)

    folders_processed, total_tokens = process_root(
        args.root, args.model, strict_children_only=not args.recursive
    )

    if folders_processed == 0:
        print("No valid 1_pass folders found with conversation.json and evaluation.json.", file=sys.stderr)
        sys.exit(2)

    # When existing counts were found, process_root already printed the average and returned.
    # When we extracted, print the average here.
    # This preserves your original output shape.
    if total_tokens >= 0:
        avg = total_tokens / folders_processed if folders_processed else 0.0
        print(f"\nAVERAGE_TOKENS_PER_RESPONSE\t{avg:.2f}")

if __name__ == "__main__":
    main()
