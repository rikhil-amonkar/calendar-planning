import argparse, asyncio, json, re, subprocess, sys, time, os
from kani import Kani
from kani.engines.openai import OpenAIEngine

PROMPT = ("Write a Python program that prints a single JSON line like "
          "{\"hello\":\"world\",\"now\":\"HH:MM\"}. Output ONLY code inside ```python fences.")

def extract_code(txt: str):
    m = re.search(r"```python\s*(.+?)```", txt, flags=re.DOTALL)
    return m.group(1).strip() if m else txt.strip()

def load_key(path):
    with open(path) as f:
        data = json.load(f)
        return data.get("deepseek")

async def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--api_key")
    ap.add_argument("--model", default="DeepSeek-R1")
    ap.add_argument("--base", default="https://api.deepseek.com")
    args = ap.parse_args()

    if args.api_key.endswith(".json"):
        args.api_key = load_key(args.api_key)

    # Initialize engine + Kani
    model = "deepseek-reasoner" if "R1" in args.model else "deepseek-chat"
    eng = OpenAIEngine(api_key=args.api_key, api_base=args.base, model=model)
    ai = Kani(eng, system_prompt="")

    # Run the usual Kani round
    msg = await ai.chat_round(PROMPT)
    resp = getattr(msg, "text", str(msg))

    # EXTRA: fetch raw OpenAI completion once to get reasoning_content
    raw = await eng.client.chat.completions.create(
        model=model,
        messages=[{"role": "user", "content": PROMPT}],
    )
    raw_msg = raw.choices[0].message
    think = getattr(raw_msg, "reasoning_content", "") or ""

    # Extract runnable code and execute
    code = extract_code(resp)
    run = subprocess.run([sys.executable, "-c", code],
                         capture_output=True, text=True)

    print("Raw Response: ", msg)
    print("\n=== Reasoning ===\n", think.strip() or "[none]")
    print("\n=== Assistant Raw ===\n", resp[:2000])
    print("\n=== Code ===\n", code)
    print("\n=== STDOUT ===\n", run.stdout.strip())
    print("\n=== STDERR ===\n", run.stderr.strip())

if __name__ == "__main__":
    asyncio.run(main())
