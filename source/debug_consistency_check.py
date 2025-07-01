#!/usr/bin/env python3

import re
import json

def test_plan_refinement_gold_extraction():
    """Test the plan refinement gold extraction with example 344 using the updated logic."""
    
    # The actual golden plan from example 344
    gold_text = """Here is the trip plan for visiting the 4 European cities for 20 days:

**Day 1-6:** Arriving in Athens and visit Athens for 6 days.
**Day 6:** Fly from Athens to Zurich.
**Day 6-11:** Visit Zurich for 6 days.
**Day 11:** Fly from Zurich to Valencia.
**Day 11-16:** Visit Valencia for 6 days.
**Day 16:** Fly from Valencia to Naples.
**Day 16-20:** Visit Naples for 5 days."""
    
    print("=== Plan Refinement Gold Extraction Test (Updated) ===")
    print("Golden plan:")
    print(gold_text)
    print("\n" + "="*50 + "\n")
    
    itinerary = []
    for line in gold_text.split('\n'):
        line = line.strip()
        if not line or not line.startswith('**Day'):
            continue
        day_match = re.search(r'Day (\d+)(?:-(\d+))?', line)
        if not day_match:
            continue
        start_day = int(day_match.group(1))
        end_day = int(day_match.group(2)) if day_match.group(2) else start_day
        day_range = f"Day {start_day}-{end_day}"
        place_match = re.search(r'(?:Arriving in|Visit|Stay in|at) ([^\s,.]+)', line, re.IGNORECASE)
        if place_match:
            itinerary.append({
                "day_range": day_range,
                "place": place_match.group(1)
            })
            print(f"Added: {day_range} in {place_match.group(1)}")
    itinerary.sort(key=lambda x: (
        int(x["day_range"].split()[1].split("-")[0]),
        x["place"]
    ))
    print(f"\nFinal itinerary: {itinerary}")
    return {"itinerary": itinerary}

def test_python_refinement_gold_extraction():
    """Test the Python refinement gold extraction approach"""
    
    # The actual golden plan from example 344
    gold_text = """Here is the trip plan for visiting the 4 European cities for 20 days:

**Day 1-6:** Arriving in Athens and visit Athens for 6 days.
**Day 6:** Fly from Athens to Zurich.
**Day 6-11:** Visit Zurich for 6 days.
**Day 11:** Fly from Zurich to Valencia.
**Day 11-16:** Visit Valencia for 6 days.
**Day 16:** Fly from Valencia to Naples.
**Day 16-20:** Visit Naples for 5 days."""
    
    print("=== Python Refinement Gold Extraction Test ===")
    print("Golden plan:")
    print(gold_text)
    print("\n" + "="*50 + "\n")
    
    itinerary = []
    
    for line in gold_text.split('\n'):
        line = line.strip()
        if not line or not line.startswith('**Day'):
            continue
            
        day_match = re.search(r'Day (\d+)(?:-(\d+))?', line)
        if not day_match:
            continue
            
        start_day = int(day_match.group(1))
        end_day = int(day_match.group(2)) if day_match.group(2) else start_day
        day_range = f"Day {start_day}-{end_day}"
        
        place_match = re.search(r'(?:Arriving in|Visit|Stay in|at) ([^\s,.]+)', line, re.IGNORECASE)
        if place_match:
            itinerary.append({
                "day_range": day_range,
                "place": place_match.group(1)
            })
            print(f"Added: {day_range} in {place_match.group(1)}")
    
    # Sort by day range start for consistent comparison
    itinerary.sort(key=lambda x: (
        int(x["day_range"].split()[1].split("-")[0]),
        x["place"]
    ))
    
    print(f"\nFinal itinerary: {itinerary}")
    return {"itinerary": itinerary}

def test_smt_refinement_gold_extraction():
    """Test the SMT refinement gold extraction approach"""
    
    # The actual golden plan from example 344
    gold_text = """Here is the trip plan for visiting the 4 European cities for 20 days:

**Day 1-6:** Arriving in Athens and visit Athens for 6 days.
**Day 6:** Fly from Athens to Zurich.
**Day 6-11:** Visit Zurich for 6 days.
**Day 11:** Fly from Zurich to Valencia.
**Day 11-16:** Visit Valencia for 6 days.
**Day 16:** Fly from Valencia to Naples.
**Day 16-20:** Visit Naples for 5 days."""
    
    print("=== SMT Refinement Gold Extraction Test ===")
    print("Golden plan:")
    print(gold_text)
    print("\n" + "="*50 + "\n")
    
    # SMT uses GPT-4.1-nano to extract, but we can simulate the expected output
    # Based on the SMT prompt, it should extract city visits only
    expected_itinerary = [
        {"day_range": "Day 1-6", "place": "Athens"},
        {"day_range": "Day 6-11", "place": "Zurich"},
        {"day_range": "Day 11-16", "place": "Valencia"},
        {"day_range": "Day 16-20", "place": "Naples"}
    ]
    
    print(f"Expected SMT extraction: {expected_itinerary}")
    return {"itinerary": expected_itinerary}

if __name__ == "__main__":
    print("Comparing gold extraction approaches across all three programs...\n")
    
    plan_result = test_plan_refinement_gold_extraction()
    print("\n" + "="*80 + "\n")
    
    python_result = test_python_refinement_gold_extraction()
    print("\n" + "="*80 + "\n")
    
    smt_result = test_smt_refinement_gold_extraction()
    print("\n" + "="*80 + "\n")
    
    print("=== COMPARISON RESULTS ===")
    print(f"Plan Refinement: {plan_result}")
    print(f"Python Refinement: {python_result}")
    print(f"SMT Refinement: {smt_result}")
    
    # Check if results are consistent
    plan_itinerary = plan_result.get("itinerary", [])
    python_itinerary = python_result.get("itinerary", [])
    smt_itinerary = smt_result.get("itinerary", [])
    
    print(f"\nConsistency check:")
    print(f"Plan vs Python: {plan_itinerary == python_itinerary}")
    print(f"Plan vs SMT: {plan_itinerary == smt_itinerary}")
    print(f"Python vs SMT: {python_itinerary == smt_itinerary}") 