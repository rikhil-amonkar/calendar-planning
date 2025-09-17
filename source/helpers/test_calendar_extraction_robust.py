#!/usr/bin/env python3

import sys
import os
import json

sys.path.append('.')
from iterative_plan_refinement_parallel import extract_answer_from_text

def test_robust_calendar_extraction():
    print("=== Robust Calendar Extraction Test ===\n")
    test_cases = [
        # Multi-line pretty-printed JSON at end
        ("The available free times for Lisa, Bobby, and Randy are compared to find a 30-minute slot where all are free, while respecting Bobby's preference to avoid meetings after 15:00.\n\n- Lisa is free from 13:00 to 16:00.\n- Bobby is free from 12:00 to 15:00 (and prefers no meetings after 15:00).\n- Randy is free from 13:30 to 14:30.\n\nThe overlapping free period is from 13:30 to 14:30. Within this window, any 30-minute slot works. For example, 13:30 to 14:00 is chosen as it satisfies all constraints and preferences.\n\n{\n  \"time_range\": \"{13:30:14:00}\",\n  \"day\": \"Monday\"\n}", {"day": "Monday", "time_range": "{13:30:14:00}"}),
        # Compact JSON at end
        ("Based on the constraints, I recommend scheduling the meeting on Monday from 13:30 to 14:00.\n\n{\"time_range\": \"{13:30:14:00}\", \"day\": \"Monday\"}", {"day": "Monday", "time_range": "{13:30:14:00}"}),
        # JSON with extra whitespace
        ("Here is the solution:\n\n{ \"time_range\": \"{13:30:14:00}\", \"day\": \"Monday\" }", {"day": "Monday", "time_range": "{13:30:14:00}"}),
        # JSON in code block
        ("Here is the proposed time:\n```json\n{\"time_range\": \"{13:30:14:00}\", \"day\": \"Monday\"}\n```", {"day": "Monday", "time_range": "{13:30:14:00}"}),
        # Natural language only (should fail)
        ("Based on the schedules, the meeting should be scheduled on Monday from 13:30 to 14:00.", None),
        # Invalid/empty (should fail)
        ("I cannot find a suitable time for the meeting.", None),
    ]
    
    for i, (input_text, expected) in enumerate(test_cases, 1):
        print(f"Test Case {i}:")
        print(f"Input: {repr(input_text[:100])}...\n")
        result = extract_answer_from_text(input_text, "calendar")
        print(f"Extracted: {result}")
        print(f"Expected: {expected}")
        success = (result == expected) if expected is not None else (result is None)
        print(f"Success: {success}")
        print("-" * 50)

def main():
    test_robust_calendar_extraction()
    print("\nAll tests completed.")

if __name__ == "__main__":
    main() 