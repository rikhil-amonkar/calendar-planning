#!/usr/bin/env python3

import re

def test_example_344():
    """Test the regex patterns with example 344's golden plan"""
    
    # The actual golden plan from example 344
    gold_text = """Here is the trip plan for visiting the 4 European cities for 20 days:

**Day 1-6:** Arriving in Athens and visit Athens for 6 days.
**Day 6:** Fly from Athens to Zurich.
**Day 6-11:** Visit Zurich for 6 days.
**Day 11:** Fly from Zurich to Valencia.
**Day 11-16:** Visit Valencia for 6 days.
**Day 16:** Fly from Valencia to Naples.
**Day 16-20:** Visit Naples for 5 days."""
    
    print("Testing regex patterns with example 344:")
    print("Golden plan:")
    print(gold_text)
    print("\n" + "="*50 + "\n")
    
    # Test the current regex patterns
    day_patterns = [
        r'\*\*Day\s+(\d+)(?:-(\d+))?\*\*:\s*(?:Arriving in|Visit|Stay in|at)?\s*([A-Za-z]+)',
        r'\*\*Day\s+(\d+)(?:-(\d+))?\*\*:\s*([A-Za-z]+)',
        r'([A-Za-z]+)\s+Day\s+(\d+)(?:-(\d+))?'
    ]
    
    for i, pattern in enumerate(day_patterns):
        print(f"Pattern {i+1}: {pattern}")
        matches = re.findall(pattern, gold_text)
        print(f"Matches: {matches}")
        print()
    
    # Test a simpler pattern
    print("Testing simpler pattern:")
    simple_pattern = r'\*\*Day\s+(\d+)-(\d+)\*\*:\s*(?:Arriving in|Visit|Stay in|at)?\s*([A-Za-z]+)'
    print(f"Simple pattern: {simple_pattern}")
    matches = re.findall(simple_pattern, gold_text)
    print(f"Matches: {matches}")
    
    # Test with raw string
    print("\nTesting with raw string:")
    raw_pattern = r'\*\*Day\s+(\d+)-(\d+)\*\*:\s*(?:Arriving in|Visit|Stay in|at)?\s*([A-Za-z]+)'
    print(f"Raw pattern: {raw_pattern}")
    matches = re.findall(raw_pattern, gold_text)
    print(f"Matches: {matches}")

if __name__ == "__main__":
    test_example_344() 