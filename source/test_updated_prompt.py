#!/usr/bin/env python3

import sys
import os

sys.path.append('.')
from iterative_plan_refinement_parallel import add_json_formatting_instruction

def test_updated_prompt():
    """Test the updated trip prompt"""
    
    print("=== Testing Updated Trip Prompt ===\n")
    
    # Create a mock example with prompt_0shot
    example = {
        "prompt_0shot": "You plan to visit 3 European cities for 10 days in total. You only take direct flights to commute between cities. You would like to visit Venice for 6 days. You have to attend a workshop in Venice between day 5 and day 10. You want to spend 2 days in Mykonos. You plan to stay in Vienna for 4 days.\n\nHere are the cities that have direct flights:\nMykonos and Vienna, Vienna and Venice.\n\nFind a trip plan of visiting the cities for 10 days by taking direct flights to commute between them."
    }
    
    # Get the updated prompt
    updated_prompt = add_json_formatting_instruction(example["prompt_0shot"], "trip")
    
    print("Updated Trip Prompt:")
    print(updated_prompt)
    
    print("\n" + "="*80 + "\n")
    
    # Check if the key instructions are present
    key_phrases = [
        "Do not include separate flight entries in the JSON output",
        "that day counts for BOTH cities",
        "The flight day (Day 3) is counted for both Venice and Vienna",
        "Do NOT create separate flight entries in the JSON"
    ]
    
    print("Checking for key instructions:")
    for phrase in key_phrases:
        if phrase in updated_prompt:
            print(f"✅ Found: {phrase}")
        else:
            print(f"❌ Missing: {phrase}")
    
    print("\n" + "="*80 + "\n")
    
    # Show the specific example in the prompt
    example_start = updated_prompt.find("If you stay in Venice from Day 1-3")
    if example_start != -1:
        example_end = updated_prompt.find("Do NOT create separate flight entries")
        if example_end != -1:
            example_section = updated_prompt[example_start:example_end + len("Do NOT create separate flight entries")]
            print("Flight Day Example in Prompt:")
            print(example_section)
        else:
            print("❌ Could not find example section")
    else:
        print("❌ Could not find flight day example")

if __name__ == "__main__":
    test_updated_prompt() 