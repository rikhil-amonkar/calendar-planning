#!/usr/bin/env python3

import json
import sys
import os

# Add the source directory to the path
sys.path.append(os.path.dirname(os.path.abspath(__file__)))

from iterative_plan_refinement_parallel import evaluate_trip

def test_flight_constraints():
    """Test flight constraint checking"""
    
    # Test constraints with direct flights
    constraints = {
        "trip_length": 5,
        "city_length": [
            {"city": "Reykjavik", "days": 2},
            {"city": "Stockholm", "days": 3}
        ],
        "direct_flights": [
            {"from": "Reykjavik", "to": "Stockholm"}
        ]
    }
    
    # Test case 1: Valid itinerary with available flight
    valid_prediction = {
        "itinerary": [
            {"day_range": "Day 1-2", "place": "Reykjavik"},
            {"day_range": "Day 3-5", "place": "Stockholm"}
        ]
    }
    
    result, violations = evaluate_trip(constraints, valid_prediction)
    print(f"Test 1 - Valid itinerary: {result}")
    if not result:
        print(f"  Violations: {violations}")
    assert result, f"Valid itinerary should pass: {violations}"
    
    # Test case 2: Invalid itinerary with unavailable flight
    invalid_prediction = {
        "itinerary": [
            {"day_range": "Day 1-2", "place": "Reykjavik"},
            {"day_range": "Day 3-5", "place": "Paris"}  # No flight from Reykjavik to Paris
        ]
    }
    
    result, violations = evaluate_trip(constraints, invalid_prediction)
    print(f"Test 2 - Invalid itinerary (unavailable flight): {result}")
    if not result:
        print(f"  Violations: {violations}")
    assert not result, "Invalid itinerary should fail"
    assert "flight" in violations, "Should have flight violation"
    assert violations["flight"]["from"] == "Reykjavik"
    assert violations["flight"]["to"] == "Paris"
    
    # Test case 3: Multiple cities with some unavailable flights
    constraints_multi = {
        "trip_length": 7,
        "city_length": [
            {"city": "Reykjavik", "days": 2},
            {"city": "Stockholm", "days": 2},
            {"city": "Paris", "days": 3}
        ],
        "direct_flights": [
            {"from": "Reykjavik", "to": "Stockholm"},
            {"from": "Stockholm", "to": "Paris"}
        ]
    }
    
    valid_multi_prediction = {
        "itinerary": [
            {"day_range": "Day 1-2", "place": "Reykjavik"},
            {"day_range": "Day 3-4", "place": "Stockholm"},
            {"day_range": "Day 5-7", "place": "Paris"}
        ]
    }
    
    result, violations = evaluate_trip(constraints_multi, valid_multi_prediction)
    print(f"Test 3 - Valid multi-city itinerary: {result}")
    if not result:
        print(f"  Violations: {violations}")
    assert result, f"Valid multi-city itinerary should pass: {violations}"
    
    # Test case 4: Invalid multi-city itinerary with unavailable flight
    invalid_multi_prediction = {
        "itinerary": [
            {"day_range": "Day 1-2", "place": "Reykjavik"},
            {"day_range": "Day 3-4", "place": "Stockholm"},
            {"day_range": "Day 5-7", "place": "London"}  # No flight from Stockholm to London
        ]
    }
    
    result, violations = evaluate_trip(constraints_multi, invalid_multi_prediction)
    print(f"Test 4 - Invalid multi-city itinerary (unavailable flight): {result}")
    if not result:
        print(f"  Violations: {violations}")
    assert not result, "Invalid multi-city itinerary should fail"
    assert "flight" in violations, "Should have flight violation"
    assert violations["flight"]["from"] == "Stockholm"
    assert violations["flight"]["to"] == "London"
    
    print("\n✅ All flight constraint tests passed!")

if __name__ == "__main__":
    test_flight_constraints() 