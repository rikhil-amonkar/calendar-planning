import json
import re
from pathlib import Path
from typing import Dict, Tuple, List

# ======================= #
# ---- CONFIG: EDIT ----  #
# ======================= #
INPUT_JSON_PATH = Path("../data/zebralogic_sample_100.json")
OUTPUT_ROOT     = Path("../output/Buckets/bucketed_result_groups/zebralogic")  # creates ./zebralogic/<bucket>/...
REPORT_PATH     = Path("../output/Buckets/constraint_summary_zebralogic.txt")
# ======================= #


# -- classification tables, exactly as provided --
SMALL = {
    (2, 2), (2, 3), (2, 4), (2, 5), (2, 6),
    (3, 2), (3, 3), (4, 2)
}
MEDIUM = {
    (3, 4), (3, 5), (3, 6), (4, 3), (4, 4),
    (5, 2), (6, 2)
}
LARGE = {
    (4, 5), (5, 3), (4, 6), (5, 4), (6, 3)
}
XLARGE = {
    (5, 5), (6, 4), (5, 6), (6, 5), (6, 6)
}


def extract_dims(name: str) -> Tuple[int, int]:
    """
    Extract NxM after 'test-' and ignore trailing '-<id>'.
    e.g. zebralogic_example_lgp-test-5x6-12 -> (5, 6)
    """
    m = re.search(r'test-(\d+)x(\d+)(?:-\d+)?', name)
    if not m:
        raise ValueError(f"Name does not contain test-NxM: {name}")
    return int(m.group(1)), int(m.group(2))


def classify_dims(dims: Tuple[int, int]) -> str:
    """
    Return one of: 'small', 'medium', 'large', 'xlarge', or 'unknown'
    """
    if dims in SMALL:
        return "small"
    if dims in MEDIUM:
        return "medium"
    if dims in LARGE:
        return "large"
    if dims in XLARGE:
        return "xlarge"
    return "unknown"


def ensure_dirs(root: Path) -> Dict[str, Path]:
    buckets = {
        "small": root / "small",
        "medium": root / "medium",
        "large": root / "large",
        "xlarge": root / "xlarge",
        "unknown": root / "unknown"  # just in case something doesn't match table
    }
    for p in buckets.values():
        p.mkdir(parents=True, exist_ok=True)
    return buckets


def write_examples(
    all_data: Dict[str, dict],
    buckets: Dict[str, Path]
) -> Dict[str, List[Tuple[str, Tuple[int, int]]]]:
    """
    Writes each example as its own JSON file in the appropriate bucket directory.

    Returns:
        mapping bucket_name -> list of (filename_with_ext, (N, M))
        to be used for report generation.
    """
    index: Dict[str, List[Tuple[str, Tuple[int, int]]]] = {
        "small": [], "medium": [], "large": [], "xlarge": [], "unknown": []
    }

    for key, value in all_data.items():
        # guarantee .json suffix and no accidental double .json
        filename = f"{key}.json" if not key.endswith(".json") else key
        try:
            dims = extract_dims(key)
        except ValueError:
            # If it can't parse, place into unknown
            dims = (-1, -1)

        bucket = classify_dims(dims) if dims != (-1, -1) else "unknown"
        out_path = buckets[bucket] / filename

        with out_path.open("w", encoding="utf-8") as f:
            json.dump(value, f, indent=2, ensure_ascii=False)

        index[bucket].append((filename, dims))

    return index


def write_report(index: Dict[str, List[Tuple[str, Tuple[int, int]]]], report_path: Path) -> None:
    """
    Report with four sections (xlarge, large, medium, small),
    listing 'filename.json: NxM - (N*M)'.
    Within each section, sort by descending area (N*M), then by filename.
    """
    order = [("xlarge", "X-Large"), ("large", "Large"), ("medium", "Medium"), ("small", "Small")]

    lines = []
    lines.append("Zebra Logic Files Ranked by Difficulty (by NxM size)")
    lines.append("=" * 55)
    lines.append("")

    for key, title in order:
        items = index.get(key, [])
        # filter out dims that failed to parse
        items = [it for it in items if it[1] != (-1, -1)]
        # sort by area desc, then filename asc
        items.sort(key=lambda t: (t[1][0] * t[1][1], t[0]), reverse=True)

        header = f"=============== {title} ==============="
        lines.append(header)
        for filename, (N, M) in items:
            area = N * M
            lines.append(f"{filename}: {N}x{M} - {area}")
        if not items:
            lines.append("(none)")
        lines.append("")  # blank line after each section

    # Unknown bucket (only if there are items)
    unknown_items = index.get("unknown", [])
    if unknown_items:
        lines.append("=============== Unknown (not in table) ===============")
        # keep as-is, but sort by filename
        unknown_items.sort(key=lambda t: t[0])
        for filename, dims in unknown_items:
            if dims == (-1, -1):
                lines.append(f"{filename}: could not parse NxM")
            else:
                N, M = dims
                area = N * M
                lines.append(f"{filename}: {N}x{M} - {area}")
        lines.append("")

    report_path.parent.mkdir(parents=True, exist_ok=True)
    report_path.write_text("\n".join(lines), encoding="utf-8")


def main():
    # 1) Load the big JSON
    with INPUT_JSON_PATH.open("r", encoding="utf-8") as f:
        all_data = json.load(f)
        if not isinstance(all_data, dict):
            raise ValueError("Top-level JSON must be an object mapping example_name -> data")

    # 2) Ensure output directories
    bucket_dirs = ensure_dirs(OUTPUT_ROOT)

    # 3) Write individual JSON files into bucket folders
    index = write_examples(all_data, bucket_dirs)

    # 4) Write the summary TXT report
    write_report(index, REPORT_PATH)

    print(f"Done.\n- Wrote per-example JSONs under: {OUTPUT_ROOT}\n- Wrote report: {REPORT_PATH}")


if __name__ == "__main__":
    main()
