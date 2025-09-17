#!/usr/bin/env python3

import json
import sys
import os

sys.path.append('.')
from iterative_plan_refinement_parallel import extract_answer_from_text, extract_gold_answer

def test_trip_flight_day_fix():
    """Test that trip extraction correctly handles flight days"""
    
    print("=== Testing Trip Flight Day Fix ===\n")
    
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
    
    print("Test Response:")
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
    
    # Check if the model's prediction matches the expected format
    if extracted and "itinerary" in extracted:
        print(f"\nModel prediction has {len(extracted['itinerary'])} city visits")
        for i, visit in enumerate(extracted['itinerary']):
            print(f"  {i+1}. {visit['place']}: {visit['day_range']}")
        
        # Check if Vienna's stay includes the flight day
        vienna_visit = next((v for v in extracted['itinerary'] if v['place'] == 'Vienna'), None)
        if vienna_visit:
            print(f"\nVienna visit: {vienna_visit['day_range']}")
            if vienna_visit['day_range'] == "Day 2-5":
                print("✅ CORRECT: Vienna includes flight day (Day 2)")
            else:
                print("❌ INCORRECT: Vienna should include flight day (Day 2)")
        else:
            print("❌ ERROR: Vienna visit not found")
    else:
        print("❌ ERROR: Failed to extract itinerary")
    
    print("\n" + "="*50 + "\n")
    
    # Test with a response that includes flight information
    test_response_with_flights = """Here is the trip plan:

```json
{
  "itinerary": [
    {
      "day_range": "Day 1-2",
      "place": "Mykonos"
    },
    {
      "flying": "Day 2",
      "from": "Mykonos",
      "to": "Vienna"
    },
    {
      "day_range": "Day 2-5",
      "place": "Vienna"
    },
    {
      "flying": "Day 5",
      "from": "Vienna",
      "to": "Venice"
    },
    {
      "day_range": "Day 5-10",
      "place": "Venice"
    }
  ]
}
```"""
    
    print("Test Response with Flight Information:")
    print(test_response_with_flights)
    print("\n" + "="*50 + "\n")
    
    # Test extraction (should filter out flight entries)
    extracted_with_flights = extract_answer_from_text(test_response_with_flights, "trip")
    print(f"Extracted (should filter flights): {extracted_with_flights}")
    
    if extracted_with_flights and "itinerary" in extracted_with_flights:
        print(f"\nFiltered itinerary has {len(extracted_with_flights['itinerary'])} city visits (flights removed)")
        for i, visit in enumerate(extracted_with_flights['itinerary']):
            print(f"  {i+1}. {visit['place']}: {visit['day_range']}")
        
        # Check if flight entries were filtered out
        flight_entries = [v for v in extracted_with_flights['itinerary'] if 'flying' in v]
        if not flight_entries:
            print("✅ CORRECT: Flight entries were filtered out")
        else:
            print("❌ ERROR: Flight entries were not filtered out")
    else:
        print("❌ ERROR: Failed to extract itinerary")

if __name__ == "__main__":
    test_trip_flight_day_fix() 