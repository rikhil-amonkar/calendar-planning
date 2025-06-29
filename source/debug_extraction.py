#!/usr/bin/env python3

import json
import sys
import os

sys.path.append('.')
from iterative_plan_refinement_parallel import extract_answer_from_text

def debug_extraction():
    """Debug the extraction function by examining actual model outputs"""
    
    # Test with some example responses that might be returned by the model
    test_responses = [
        # Example 1: JSON in code blocks
        '''Here is the proposed time:
```json
{"time_range": "{14:30:15:30}", "day": "Tuesday"}
```''',
        
        # Example 2: Plain JSON
        '''The meeting time is: {"time_range": "{14:30:15:30}", "day": "Tuesday"}''',
        
        # Example 3: Natural language
        '''I suggest we meet on Tuesday from 14:30 to 15:30.''',
        
        # Example 4: Different format
        '''Tuesday, 14:30 - 15:30''',
        
        # Example 5: Empty or malformed
        '''I cannot find a suitable time for the meeting.''',
        
        # Example 6: What the model might actually be returning
        '''Based on the constraints, I recommend scheduling the meeting on Tuesday from 2:30 PM to 3:30 PM.''',
    ]
    
    print("=== Debugging Calendar Extraction ===")
    print()
    
    for i, response in enumerate(test_responses, 1):
        print(f"Test {i}:")
        print(f"Input: {repr(response)}")
        print(f"Output: {extract_answer_from_text(response, 'calendar')}")
        print("-" * 50)
    
    # Now let's check what's actually in the output files
    print("\n=== Checking Actual Model Outputs ===")
    
    output_dir = "../output/Plan/meta-llama/Llama-3.1-8B-Instruct/calendar/n_pass"
    if os.path.exists(output_dir):
        for example_dir in os.listdir(output_dir):
            example_path = os.path.join(output_dir, example_dir)
            if os.path.isdir(example_path):
                # Check the first pass
                pass_dir = os.path.join(example_path, "1_pass")
                if os.path.exists(pass_dir):
                    conversation_file = os.path.join(pass_dir, "conversation.json")
                    if os.path.exists(conversation_file):
                        try:
                            with open(conversation_file, 'r') as f:
                                conversation = json.load(f)
                            
                            # Find the assistant's response
                            for msg in conversation:
                                if msg.get("role") == "assistant":
                                    response = msg.get("content", "")
                                    print(f"\nExample: {example_dir}")
                                    print(f"Model Response: {repr(response[:200])}...")
                                    extracted = extract_answer_from_text(response, 'calendar')
                                    print(f"Extracted: {extracted}")
                                    break
                        except Exception as e:
                            print(f"Error reading {conversation_file}: {e}")

if __name__ == "__main__":
    debug_extraction() 