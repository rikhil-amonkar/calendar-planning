#!/usr/bin/env python3
"""
Simple test script to check if Qwen2.5 models output reasoning.
Run from terminal with: python test_qwen25_reasoning.py --model Qwen/Qwen2.5-Coder-32B-Instruct
"""

import argparse
import asyncio
import re
import sys
from kani import Kani
from kani.engines.huggingface import HuggingEngine
from transformers import AutoTokenizer, AutoModelForCausalLM

# Simple test prompts - one with explicit reasoning instructions, one without
PROMPT_WITH_REASONING = """Solve this problem step by step.

Problem: You need to schedule a meeting for Alice and Bob for 30 minutes between 9:00 and 17:00 on Monday. 
Alice is busy from 10:00-11:00 and 14:00-15:00. Bob is busy from 9:30-10:30 and 13:00-14:00.

Please reason step by step about how to solve this problem. Enclose your reasoning process within <reasoning> and </reasoning> tags, then provide your solution code. Use this format:

<reasoning>
Your step-by-step reasoning here...
</reasoning>

Then provide your code solution.

Write a Python program that solves it. Always surround your final code with ```python
YOUR_CODE
```."""

PROMPT_WITHOUT_REASONING = """Solve this problem.

Problem: You need to schedule a meeting for Alice and Bob for 30 minutes between 9:00 and 17:00 on Monday. 
Alice is busy from 10:00-11:00 and 14:00-15:00. Bob is busy from 9:30-10:30 and 13:00-14:00.

Write a Python program that solves it. Always surround your final code with ```python
YOUR_CODE
```."""

def extract_reasoning_tags(text):
    """Extract reasoning from <reasoning> or <think> tags"""
    # Try <reasoning> tags first
    match = re.search(r'<reasoning>(.*?)</reasoning>', text, re.DOTALL | re.IGNORECASE)
    if match:
        return match.group(1).strip()
    # Try <think> tags
    match = re.search(r'<think>(.*?)</think>', text, re.DOTALL | re.IGNORECASE)
    if match:
        return match.group(1).strip()
    return None

def extract_reasoning_text(text):
    """Extract reasoning from text before code blocks"""
    code_start = text.find("```")
    if code_start > 50:  # Substantial text before code
        potential_reasoning = text[:code_start].strip()
        # Check if it looks like reasoning
        reasoning_keywords = ["think", "analyze", "consider", "reason", "approach", "strategy",
                             "understand", "need", "must", "should", "constraint", "solution",
                             "first", "then", "because", "therefore", "step", "problem",
                             "given", "calculate", "determine", "find", "solve"]
        if len(potential_reasoning) > 50 and any(keyword in potential_reasoning.lower() for keyword in reasoning_keywords):
            return potential_reasoning
        elif len(potential_reasoning) > 200:  # Very substantial text
            return potential_reasoning
    return None

def extract_code(text):
    """Extract code from markdown code blocks"""
    match = re.search(r"```python\s*(.+?)```", text, flags=re.DOTALL)
    if match:
        return match.group(1).strip()
    # Fallback: try without language specifier
    match = re.search(r"```\s*(.+?)```", text, flags=re.DOTALL)
    if match:
        return match.group(1).strip()
    return None

async def test_model(model_name, use_reasoning_instructions=True):
    """Test Qwen2.5 model and check for reasoning output"""
    print(f"\n{'='*80}")
    print(f"Testing model: {model_name}")
    print(f"Reasoning instructions: {'YES' if use_reasoning_instructions else 'NO'}")
    print(f"{'='*80}\n")
    
    # Load model
    print("Loading model...")
    try:
        HF_CACHE_DIR = "./.cache/huggingface"
        
        tok = AutoTokenizer.from_pretrained(
            model_name,
            cache_dir=HF_CACHE_DIR,
            trust_remote_code=True,
        )
        mdl = AutoModelForCausalLM.from_pretrained(
            model_name,
            cache_dir=HF_CACHE_DIR,
            device_map="auto",
            torch_dtype="auto",
            trust_remote_code=True,
        )
        
        # Set up tokenizer for Qwen
        if tok.pad_token_id is None:
            tok.pad_token = tok.eos_token
        tok.padding_side = "left"
        mdl.config.pad_token_id = tok.pad_token_id
        mdl.eval()
        
        # Create engine
        engine = HuggingEngine(model_id=model_name)
        engine.model = mdl
        engine.tokenizer = tok
        
        # Configure generation
        engine.encode_kwargs = {
            "padding": True,
            "truncation": True,
            "return_tensors": "pt",
        }
        gen = getattr(engine, "generation_kwargs", {}) or {}
        gen.setdefault("pad_token_id", tok.pad_token_id)
        gen.setdefault("eos_token_id", tok.eos_token_id)
        gen.setdefault("max_new_tokens", 2048)  # More tokens for reasoning
        gen.setdefault("do_sample", False)
        gen.setdefault("temperature", 0.0)
        engine.generation_kwargs = gen
        
        print("Model loaded successfully!\n")
    except Exception as e:
        print(f"ERROR loading model: {e}")
        return
    
    # Set up system prompt for reasoning models
    system_prompt = ""
    if "qwen" in model_name.lower() and ("2.5" in model_name.lower() or "reasoning" in model_name.lower()):
        system_prompt = (
            "You are a helpful AI assistant. When solving problems, provide detailed reasoning in <reasoning> tags, "
            "then provide your solution or code. Use this format:\n"
            "<reasoning>\n"
            "Your step-by-step reasoning here...\n"
            "</reasoning>\n"
            "Then provide your code solution."
        )
        print("Added reasoning system prompt\n")
    
    # Create Kani instance
    ai = Kani(engine, system_prompt=system_prompt)
    
    # Select prompt
    prompt = PROMPT_WITH_REASONING if use_reasoning_instructions else PROMPT_WITHOUT_REASONING
    
    print(f"Prompt:\n{'-'*80}\n{prompt}\n{'-'*80}\n")
    print("Running model...\n")
    
    # Run model
    try:
        msg = await ai.chat_round(prompt)
        response = getattr(msg, "text", str(msg))
        
        print(f"{'='*80}")
        print("RAW RESPONSE (first 3000 chars):")
        print(f"{'='*80}\n")
        print(response[:3000])
        if len(response) > 3000:
            print(f"\n... (truncated, total length: {len(response)} chars)\n")
        
        # Try to extract reasoning
        reasoning_from_tags = extract_reasoning_tags(response)
        reasoning_from_text = extract_reasoning_text(response)
        code = extract_code(response)
        
        print(f"\n{'='*80}")
        print("REASONING EXTRACTION RESULTS:")
        print(f"{'='*80}\n")
        
        if reasoning_from_tags:
            print(f"✓ Found reasoning in TAGS (<reasoning> or <think>):")
            print(f"  Length: {len(reasoning_from_tags)} chars")
            print(f"\n{reasoning_from_tags[:500]}")
            if len(reasoning_from_tags) > 500:
                print("  ... (truncated)")
        else:
            print("✗ No reasoning found in TAGS")
        
        if reasoning_from_text and not reasoning_from_tags:
            print(f"\n✓ Found reasoning in TEXT (before code):")
            print(f"  Length: {len(reasoning_from_text)} chars")
            print(f"\n{reasoning_from_text[:500]}")
            if len(reasoning_from_text) > 500:
                print("  ... (truncated)")
        elif not reasoning_from_tags:
            print("\n✗ No substantial reasoning found in TEXT before code")
        
        print(f"\n{'='*80}")
        print("CODE EXTRACTION:")
        print(f"{'='*80}\n")
        if code:
            print(f"✓ Found code ({len(code)} chars)")
            print(f"\n{code[:500]}")
            if len(code) > 500:
                print("  ... (truncated)")
        else:
            print("✗ No code found in response")
        
        # Summary
        print(f"\n{'='*80}")
        print("SUMMARY:")
        print(f"{'='*80}")
        print(f"Total response length: {len(response)} chars")
        print(f"Reasoning found: {'YES' if (reasoning_from_tags or reasoning_from_text) else 'NO'}")
        if reasoning_from_tags:
            print(f"  - In tags: {len(reasoning_from_tags)} chars")
        if reasoning_from_text and not reasoning_from_tags:
            print(f"  - In text: {len(reasoning_from_text)} chars")
        print(f"Code found: {'YES' if code else 'NO'}")
        if code:
            print(f"  - Code length: {len(code)} chars")
        
    except Exception as e:
        print(f"ERROR running model: {e}")
        import traceback
        traceback.print_exc()

async def main():
    parser = argparse.ArgumentParser(
        description="Test Qwen2.5 model reasoning output",
        formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument(
        "--model",
        type=str,
        default="Qwen/Qwen2.5-Coder-32B-Instruct",
        help="Model name/path (default: Qwen/Qwen2.5-Coder-32B-Instruct)"
    )
    parser.add_argument(
        "--no-reasoning-instructions",
        action="store_true",
        help="Test without explicit reasoning instructions in prompt"
    )
    
    args = parser.parse_args()
    
    await test_model(args.model, use_reasoning_instructions=not args.no_reasoning_instructions)

if __name__ == "__main__":
    asyncio.run(main())
