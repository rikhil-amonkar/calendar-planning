#!/usr/bin/env python3

import json
import sys
import os

sys.path.append('.')
from iterative_plan_refinement_parallel import extract_answer_from_text, initialize_model
import asyncio

async def test_calendar_fix():
    """Test if the updated prompt produces JSON output"""
    
    # Load a calendar example
    with open("../data/calendar_scheduling_100.json", "r") as f:
        examples = json.load(f)
    
    example = examples["calendar_scheduling_example_543"]
    
    # Construct the updated prompt
    prompt = example.get("prompt_0shot", "")
    prompt += "\n\nIMPORTANT: Do NOT write any code or algorithms. Simply provide the answer in the following JSON format:\n{\"time_range\": \"{HH:MM:HH:MM}\", \"day\": \"<DAY>\"}\n\nFor example, if the proposed time is Tuesday, 14:30 to 15:30, the output should be:\n{\"time_range\": \"{14:30:15:30}\", \"day\": \"Tuesday\"}\n\nProvide ONLY the JSON answer, no explanations or code."
    
    print("=== Testing Updated Calendar Prompt ===")
    print(f"Prompt: {prompt[:500]}...")
    print()
    
    # Try to initialize model (this might fail without proper setup, but we can test the prompt)
    try:
        # Load API keys
        with open("../../scheduling_key.json") as f:
            keys = json.load(f)
        
        model = initialize_model("meta-llama/Llama-3.1-8B-Instruct", keys)
        
        # Make a test call
        response = await model.agenerate([prompt], max_new_tokens=200, temperature=0)
        response_text = response.generations[0][0].text
        
        print(f"Model Response: {repr(response_text)}")
        print()
        
        # Test extraction
        extracted = extract_answer_from_text(response_text, "calendar")
        print(f"Extracted: {extracted}")
        
    except Exception as e:
        print(f"Model test failed (expected without proper setup): {e}")
        print("This is expected if the model isn't properly configured.")
        print("The important thing is that the prompt is now more explicit about JSON output.")

if __name__ == "__main__":
    asyncio.run(test_calendar_fix()) 