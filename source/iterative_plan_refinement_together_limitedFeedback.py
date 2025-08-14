import argparse
import json
import os
import asyncio
import re
import time
import logging
import shutil
from openai import OpenAI
import httpx
from typing import Dict, Any

from iterative_plan_refinement_parallel import (
    parse_args,
    get_task_prompt,
    add_json_formatting_instruction,
    evaluate_calendar,
    evaluate_meeting,
    evaluate_trip,
    normalize_trip_itinerary,
    extract_answer_from_text,
    format_constraint_feedback,
    check_exact_match,
    RateLimiter,
    load_examples,
    load_constraints,
    extract_gold_answer
)

# Set up logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    handlers=[
        logging.FileHandler('iterative_plan_refinement_together.log'),
        logging.StreamHandler()
    ]
)

TOGETHER_API_KEY = "45dc2c46ec1b95e0a28d5ea72e9db50f18bfd9adea69660d5d0b2be124f8729c"
TOGETHER_API_URL = "https://api.together.xyz/v1/chat/completions"

async def together_chat_completion(model, messages, max_tokens=2048, temperature=0.0, stop=None):
    headers = {
        "Authorization": f"Bearer {TOGETHER_API_KEY}",
        "Content-Type": "application/json"
    }
    payload = {
        "model": model,
        "messages": messages,
        "max_tokens": max_tokens,
        "temperature": temperature,
    }
    if stop:
        payload["stop"] = stop
    async with httpx.AsyncClient(timeout=60) as client:
        response = await client.post(TOGETHER_API_URL, headers=headers, json=payload)
        response.raise_for_status()
        return response.json()["choices"][0]["message"]["content"]

async def process_single_example_together(
    example_id,
    example,
    constraints,
    model,
    max_passes,
    rate_limiter,
    semaphore,
    task,
    args
):
    async with semaphore:
        output_dir = f"../output/Plan/{model}/{task}/n_pass/{example_id}"
        os.makedirs(output_dir, exist_ok=True)
        conversation_history = []
        gold_text = extract_gold_answer(example, task)
        gold_formatted = extract_answer_from_text(gold_text, task) if gold_text else {}
        current_prompt = add_json_formatting_instruction(get_task_prompt(task, example), task)
        messages = [
            {"role": "user", "content": current_prompt}
        ]
        pred_formatted = {}
        violated_constraints = {}
        is_exact_match = False
        constraints_satisfied = False
        response_text = ""
        for pass_num in range(1, max_passes + 1):
            pass_output_dir = f"{output_dir}/{pass_num}_pass"
            os.makedirs(pass_output_dir, exist_ok=True)
            is_openai = model.startswith("gpt") or model.startswith("o")
            try:
                await rate_limiter.wait()
                if is_openai:
                    openai_key = os.getenv("OPENAI_API_KEY")
                    if not openai_key:
                        with open("../scheduling_key.json") as f:
                            openai_key = json.load(f)["openai"]
                    client = OpenAI(api_key=openai_key)
                    response = client.chat.completions.create(
                        model=model,
                        messages=messages,
                        temperature=0,
                        max_tokens=2048
                    )
                    response_text = response.choices[0].message.content
                else:
                    response_text = await together_chat_completion(model, messages, max_tokens=2048, temperature=0.0)
                conversation_history.append({"role": "user", "content": messages[-1]["content"]})
                conversation_history.append({"role": "assistant", "content": response_text})
                messages.append({"role": "assistant", "content": response_text})
                with open(f"{pass_output_dir}/conversation.json", "w") as f:
                    json.dump(conversation_history, f, indent=4)
                pred_formatted = extract_answer_from_text(response_text, task)
                with open(f"{pass_output_dir}/plan.json", "w") as f:
                    json.dump(pred_formatted, f, indent=4)
                
                # Handle empty prediction cases
                if pred_formatted == {} or pred_formatted is None:
                    constraints_satisfied = False
                    violated_constraints = {}
                    is_exact_match = False
                    status = "No plan found"
                else:
                    # Only evaluate constraints if we have a valid prediction
                    if task == "calendar":
                        constraints_satisfied, violated_constraints = evaluate_calendar(constraints, pred_formatted)
                    elif task == "meeting":
                        constraints_satisfied, violated_constraints = evaluate_meeting(constraints, pred_formatted)
                    elif task == "trip":
                        constraints_satisfied, violated_constraints = evaluate_trip(constraints, pred_formatted)
                    
                    is_exact_match = check_exact_match(gold_formatted, pred_formatted, task) if gold_formatted and pred_formatted else False
                    
                    # Determine status - check exact match first, then constraints
                    if is_exact_match:
                        status = "Exact match"
                        constraints_satisfied = True
                    elif constraints_satisfied:
                        status = "Correct plan (constraints satisfied)"
                    else:
                        status = "Wrong plan"
                
                eval_result = {
                    "has_execution_error": False,
                    "execution_output": response_text,
                    "pred": pred_formatted,
                    "gold": gold_formatted if gold_text and pred_formatted else {},
                    "status": status,
                    "violated_constraint": violated_constraints,
                    "is_exact_match": is_exact_match,
                    "constraints_satisfied": constraints_satisfied,
                    "pass_number": pass_num
                }
                with open(f"{pass_output_dir}/evaluation.json", "w") as f:
                    json.dump(eval_result, f, indent=4)
                
                if is_exact_match or constraints_satisfied:
                    logging.info(f"[{example_id}] SUCCESS! Solved in pass {pass_num}")
                    return
                elif pred_formatted == {} or pred_formatted is None:
                    current_prompt = f"The previous solution produced the following output:\n{response_text}\nHowever, it fails to find a solution.\n\nPlease generate a valid solution."
                    messages.append({"role": "user", "content": current_prompt})
                else:
                    current_prompt = f"The previous solution produced the following output:\n{response_text}\nHowever, the solution is incorrect.\n\nPlease generate a valid solution."
                    messages.append({"role": "user", "content": current_prompt})
            except Exception as e:
                logging.error(f"[{example_id}] Unexpected error: {str(e)}")
                error_eval_result = {
                    "has_execution_error": True,
                    "execution_output": f"Unexpected error: {str(e)}",
                    "pred": {},
                    "gold": {},
                    "status": "Unexpected error",
                    "violated_constraint": {},
                    "is_exact_match": False,
                    "constraints_satisfied": False,
                    "pass_number": pass_num
                }
                with open(f"{pass_output_dir}/evaluation.json", "w") as f:
                    json.dump(error_eval_result, f, indent=4)
                continue

async def main():
    args = parse_args()
    examples = load_examples(args.task)
    constraints = load_constraints(args.task)
    if args.examples:
        example_numbers = [int(x) for x in args.examples.split(',')]
        examples = {k: v for k, v in examples.items() if any(str(num) in k for num in example_numbers)}
    elif args.start is not None or args.end is not None:
        start = args.start or 0
        end = args.end or len(examples)
        example_items = list(examples.items())[start:end]
        examples = dict(example_items)
    logging.info(f"Starting processing of {len(examples)} examples")
    rate_limiter = RateLimiter(args.rate_limit)
    semaphore = asyncio.Semaphore(args.max_concurrent)
    tasks = []
    for example_id, example in examples.items():
        tasks.append(process_single_example_together(
            example_id,
            example,
            constraints.get(example_id, {}),
            args.model,
            args.max_passes,
            rate_limiter,
            semaphore,
            args.task,
            args
        ))
    await asyncio.gather(*tasks, return_exceptions=True)

if __name__ == "__main__":
    asyncio.run(main())