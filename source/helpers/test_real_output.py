#!/usr/bin/env python3

import sys
import os
import json

sys.path.append('.')
from iterative_plan_refinement_parallel import extract_answer_from_text

def test_real_output():
    print("=== Testing with Real Model Output ===\n")
    
    # Read the actual model output from the file
    conversation_file = "../output/Plan/DeepSeek-R1/calendar/n_pass/calendar_scheduling_example_33/1_pass/conversation.json"
    
    try:
        with open(conversation_file, 'r') as f:
            conversation = json.load(f)
        
        # Find the assistant's response
        for msg in conversation:
            if msg.get("role") == "assistant":
                model_output = msg.get("content", "")
                print(f"Model Output:\n{model_output}\n")
                
                # Test extraction
                extracted = extract_answer_from_text(model_output, "calendar")
                print(f"Extracted: {extracted}")
                
                # Expected result
                expected = {"day": "Monday", "time_range": "{13:30:14:00}"}
                print(f"Expected: {expected}")
                print(f"Success: {extracted == expected}")
                break
                
    except Exception as e:
        print(f"Error reading file: {e}")

if __name__ == "__main__":
    test_real_output() 