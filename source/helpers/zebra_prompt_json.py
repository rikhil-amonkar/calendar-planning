# sample_zebralogic.py
import json
import random
import argparse
from pathlib import Path

from datasets import load_dataset

def to_record(example):
    """
    Convert a ZebraLogic example into your expected schema.
    """
    # example has keys like: id, puzzle, solution
    # We'll store as zebralogic_example_{id}
    key = f"zebralogic_example_{example['id']}"

    # Optional: derive simple metadata
    sol = example["solution"]
    num_houses = len(sol.get("rows", []))
    num_attributes = len(sol.get("header", []))

    rec = {
        "prompt_0shot": example["puzzle"],
        "golden_plan": sol,
        "meta": {
            "num_houses": num_houses,
            "num_attributes": num_attributes
        }
    }
    return key, rec

def sample_uniform(ds, k, seed):
    random.seed(seed)
    idxs = random.sample(range(len(ds)), k)
    return [ds[i] for i in idxs]

def sample_stratified_by_houses(ds, k, seed):
    """
    Simple stratified sampling by number of houses inferred from solution rows.
    Tries to allocate evenly across buckets.
    """
    random.seed(seed)
    buckets = {}
    for ex in ds:
        n = len(ex["solution"].get("rows", []))
        buckets.setdefault(n, []).append(ex)
    # even allocation across buckets
    sizes = sorted(buckets.keys())
    out = []
    per_bucket = max(1, k // max(1, len(sizes)))
    for n in sizes:
        pool = buckets[n]
        take = min(per_bucket, len(pool))
        out.extend(random.sample(pool, take))
    # fill remainder if needed
    if len(out) < k:
        remaining = [ex for ex in ds if ex not in out]
        need = k - len(out)
        out.extend(random.sample(remaining, need))
    return out[:k]

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--count", type=int, default=100, help="number of examples to sample")
    ap.add_argument("--seed", type=int, default=42, help="random seed")
    ap.add_argument("--split", type=str, default="test", help="dataset split to use")
    ap.add_argument("--config", type=str, default="grid_mode", help="dataset config")
    ap.add_argument("--out", type=str, default="zebralogic_sample_100.json", help="output JSON path")
    ap.add_argument("--mode", choices=["uniform", "stratified"], default="uniform",
                    help="uniform random or stratified by number of houses")
    args = ap.parse_args()

    ds = load_dataset("WildEval/ZebraLogic", args.config, split=args.split)

    if args.count > len(ds):
        raise ValueError(f"Requested {args.count} but split has only {len(ds)} examples")

    if args.mode == "uniform":
        picked = sample_uniform(ds, args.count, args.seed)
    else:
        picked = sample_stratified_by_houses(ds, args.count, args.seed)

    output = {}
    for ex in picked:
        key, rec = to_record(ex)
        output[key] = rec

    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    with open(out_path, "w") as f:
        json.dump(output, f, indent=2)

    print(f"Wrote {len(output)} examples to {out_path.resolve()}")

if __name__ == "__main__":
    main()
