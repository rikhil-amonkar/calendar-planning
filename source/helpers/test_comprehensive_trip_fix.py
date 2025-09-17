#!/usr/bin/env python3

import json
import sys
import os

sys.path.append('.')
from iterative_plan_refinement_parallel import extract_answer_from_text, evaluate_trip, add_json_formatting_instruction

def test_comprehensive_trip_fix():
    """Test all trip fixes together"""
    
    print("=== Comprehensive Trip Fix Test ===\n")
    
    # Test case from example 21
    test_response = """The trip plan must satisfy the following constraints:
- Total trip duration is 10 days.
- Venice must be visited for 6 days, including the workshop period between day 5 and day 10. Therefore, Venice is scheduled for days 5-10 to ensure full coverage of the workshop.
- Mykonos must be visited for 2 days.
- Vienna must be visited for 4 days, but due to the fixed Venice period (days 5-10) and the 10-day total, Vienna can only be accommodated for 2 days in this itinerary (days 3-4) to allow for the Mykonos visit.
- Direct flights are available between Mykonos and Vienna, and between Vienna and Venice, so the itinerary uses these connections: Mykonos to Vienna, then Vienna to Venice.
- Flight days are not included in the JSON output, as per the requirement.

The itinerary is as follows:
- Days 1-2: Mykonos (2-day stay)
- Days 3-4: Vienna (2-day stay, as 4 days are not possible with the constraints)
- Days 5-10: Venice (6-day stay, covering the workshop period)

This plan uses direct flights for commuting and fits within the 10-day total.

```json
{
  "itinerary": [
    {
      "day_range": "Day 1-2",
      "place": "Mykonos"
    },
    {
      "day_range": "Day 3-4",
      "place": "Vienna"
    },
    {
      "day_range": "Day 5-10",
      "place": "Venice"
    }
  ]
}
```"""
    
    print("1. Testing Model Response Extraction:")
    print("Model Response:")
    print(test_response)
    print("\n" + "="*50 + "\n")
    
    # Test extraction
    extracted = extract_answer_from_text(test_response, "trip")
    print(f"Extracted prediction: {extracted}")
    
    # Expected gold format (from the evaluation)
    expected_gold = {
        "itinerary": [
            {"day_range": "Day 1-2", "place": "Mykonos"},
            {"day_range": "Day 2-5", "place": "Vienna"},  # Note: Day 2 is included in Vienna's stay
            {"day_range": "Day 5-10", "place": "Venice"}
        ]
    }
    
    print(f"\nExpected gold: {expected_gold}")
    
    print("\n" + "="*50 + "\n")
    
    # Test 2: Check if the model's prediction would satisfy constraints if it included flight days
    print("2. Testing Constraint Evaluation:")
    
    # Constraints for example 21
    constraints = {
        "trip_length": 10,
        "city_length": [
            {"city": "Mykonos", "days": 2},
            {"city": "Vienna", "days": 4},
            {"city": "Venice", "days": 6}
        ]
    }
    
    print(f"Constraints: {constraints}")
    
    # Test with model's prediction (incorrect - doesn't include flight days)
    print(f"\nTesting model's prediction:")
    satisfied, violations = evaluate_trip(constraints, extracted)
    print(f"Constraints satisfied: {satisfied}")
    print(f"Violations: {violations}")
    
    # Test with expected gold (correct - includes flight days)
    print(f"\nTesting expected gold:")
    satisfied_gold, violations_gold = evaluate_trip(constraints, expected_gold)
    print(f"Constraints satisfied: {satisfied_gold}")
    print(f"Violations: {violations_gold}")
    
    print("\n" + "="*50 + "\n")
    
    # Test 3: Check the updated prompt
    print("3. Testing Updated Prompt:")
    
    example = {
        "prompt_0shot": "You plan to visit 3 European cities for 10 days in total. You only take direct flights to commute between cities. You would like to visit Venice for 6 days. You have to attend a workshop in Venice between day 5 and day 10. You want to spend 2 days in Mykonos. You plan to stay in Vienna for 4 days.\n\nHere are the cities that have direct flights:\nMykonos and Vienna, Vienna and Venice.\n\nFind a trip plan of visiting the cities for 10 days by taking direct flights to commute between them."
    }
    
    updated_prompt = add_json_formatting_instruction(example["prompt_0shot"], "trip")
    
    # Check if key instructions are present
    key_phrases = [
        "that day counts for BOTH cities",
        "The flight day (Day 3) is counted for both Venice and Vienna",
        "Do NOT create separate flight entries in the JSON"
    ]
    
    print("Checking updated prompt for key instructions:")
    for phrase in key_phrases:
        if phrase in updated_prompt:
            print(f"✅ Found: {phrase}")
        else:
            print(f"❌ Missing: {phrase}")
    
    print("\n" + "="*50 + "\n")
    
    # Test 4: Trip length calculation with overlapping days
    print("4. Testing Trip Length Calculation:")
    
    # Test case with overlapping days
    test_itinerary = {
        "itinerary": [
            {"day_range": "Day 1-2", "place": "Mykonos"},
            {"day_range": "Day 2-5", "place": "Vienna"},  # Day 2 overlaps with Mykonos
            {"day_range": "Day 5-10", "place": "Venice"}  # Day 5 overlaps with Vienna
        ]
    }
    
    # This should be 10 days total (Day 1,2,3,4,5,6,7,8,9,10)
    test_constraints = {"trip_length": 10}
    
    satisfied_length, violations_length = evaluate_trip(test_constraints, test_itinerary)
    print(f"Test itinerary: {test_itinerary}")
    print(f"Expected trip length: 10 days")
    print(f"Constraints satisfied: {satisfied_length}")
    print(f"Violations: {violations_length}")
    
    if satisfied_length:
        print("✅ Trip length calculation works correctly with overlapping days")
    else:
        print("❌ Trip length calculation has issues")

if __name__ == "__main__":
    test_comprehensive_trip_fix() 