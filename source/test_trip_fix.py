#!/usr/bin/env python3

import json
import sys
import os

sys.path.append('.')
from iterative_plan_refinement_parallel import extract_gold_answer, evaluate_trip, extract_answer_from_text

def test_trip_fixes():
    """Test the trip fixes"""
    
    print("=== Testing Trip Fixes ===")
    
    # Test 1: Gold extraction
    print("\n1. Testing gold extraction:")
    
    # Load a trip example
    with open("../data/trip_planning_100.json", "r") as f:
        examples = json.load(f)
    
    # Find an example with a good golden plan
    for example_id, example in examples.items():
        if "golden_plan" in example and example["golden_plan"]:
            print(f"Testing with {example_id}")
            gold_formatted = extract_gold_answer(example, "trip")
            print(f"Gold formatted: {gold_formatted}")
            break
    
    # Test 2: Evaluation logic
    print("\n2. Testing evaluation logic:")
    
    # Test constraints
    test_constraints = {
        "trip_length": 20,
        "city_length": [
            {"city": "Valencia", "days": 6},
            {"city": "Athens", "days": 6},
            {"city": "Naples", "days": 5},
            {"city": "Zurich", "days": 6}
        ],
        "city_day_ranges": [
            {"city": "Athens", "start": 1, "end": 6},
            {"city": "Naples", "start": 16, "end": 20}
        ],
        "direct_flights": [
            {"from": "Valencia", "to": "Athens"},
            {"from": "Valencia", "to": "Zurich"},
            {"from": "Zurich", "to": "Naples"}
        ]
    }
    
    # Test prediction (only city visits, no flights)
    test_prediction = {
        "itinerary": [
            {"day_range": "Day 1-6", "place": "Athens"},
            {"day_range": "Day 6-11", "place": "Valencia"},
            {"day_range": "Day 11-16", "place": "Zurich"},
            {"day_range": "Day 16-20", "place": "Naples"}
        ]
    }
    
    constraints_satisfied, violated_constraints = evaluate_trip(test_constraints, test_prediction)
    print(f"Constraints satisfied: {constraints_satisfied}")
    print(f"Violated constraints: {violated_constraints}")
    
    # Test 3: Extraction function
    print("\n3. Testing extraction function:")
    
    test_response = '''Here is the trip plan:
```json
{
  "itinerary": [
    {
      "day_range": "Day 1-6",
      "place": "Athens"
    },
    {
      "flying": "Day 6",
      "from": "Athens",
      "to": "Valencia"
    },
    {
      "day_range": "Day 6-11",
      "place": "Valencia"
    }
  ]
}
```'''
    
    extracted = extract_answer_from_text(test_response, "trip")
    print(f"Extracted (should only have city visits): {extracted}")
    
    print("\n=== Trip Fixes Test Complete ===")

if __name__ == "__main__":
    test_trip_fixes() 