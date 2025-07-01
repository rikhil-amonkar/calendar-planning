#!/usr/bin/env python3

import re

def test_gold_extraction():
    """Test the gold extraction regex patterns"""
    
    # Test with the actual golden plan format from example 1088
    gold_text = """Here is the trip plan for visiting the 8 European cities for 21 days:

**Day 1-2:** Arriving in Reykjavik and visit Reykjavik for 2 days.
**Day 2:** Fly from Reykjavik to Stockholm.
**Day 2-4:** Visit Stockholm for 3 days.
**Day 4:** Fly from Stockholm to Tallinn.
**Day 4-8:** Visit Tallinn for 5 days.
**Day 8:** Fly from Tallinn to Oslo.
**Day 8-12:** Visit Oslo for 5 days.
**Day 12:** Fly from Oslo to Geneva.
**Day 12-13:** Visit Geneva for 2 days.
**Day 13:** Fly from Geneva to Split.
**Day 13-15:** Visit Split for 3 days.
**Day 15:** Fly from Split to Stuttgart.
**Day 15-19:** Visit Stuttgart for 5 days.
**Day 19:** Fly from Stuttgart to Porto.
**Day 19-21:** Visit Porto for 3 days."""
    
    print("Testing gold extraction patterns:")
    print("=" * 50)
    
    # Test simpler patterns
    day_patterns = [
        r'\*\*Day\s+(\d+)(?:-(\d+))?\*\*:\s*(?:Arriving in|Visit|Stay in|at)?\s*([A-Za-z]+)',
        r'\*\*Day\s+(\d+)(?:-(\d+))?\*\*:\s*([A-Za-z]+)',
        r'Day\s+(\d+)(?:-(\d+))?:\s*(?:Arriving in|Visit|Stay in|at)?\s*([A-Za-z]+)',
        r'Day\s+(\d+)(?:-(\d+))?:\s*([A-Za-z]+)'
    ]
    
    itinerary = []
    
    for i, pattern in enumerate(day_patterns):
        print(f"\nPattern {i+1}: {pattern}")
        matches = re.findall(pattern, gold_text, re.IGNORECASE)
        print(f"Matches: {matches}")
        
        for match in matches:
            if len(match) >= 2:
                if match[0].isdigit():  # First pattern
                    start_day = int(match[0])
                    end_day = int(match[1]) if match[1] and match[1].isdigit() else start_day
                    city = match[2].strip()
                elif match[1].isdigit():  # Third pattern
                    city = match[0].strip()
                    start_day = int(match[1])
                    end_day = int(match[2]) if match[2] and match[2].isdigit() else start_day
                else:
                    continue
                
                itinerary.append({
                    "day_range": f"Day {start_day}-{end_day}",
                    "place": city
                })
                print(f"  -> {city}: Day {start_day}-{end_day}")
    
    # Remove duplicates and sort
    seen = set()
    unique_itinerary = []
    for item in itinerary:
        key = (item["day_range"], item["place"])
        if key not in seen:
            seen.add(key)
            unique_itinerary.append(item)
    
    # Sort by start day
    unique_itinerary.sort(key=lambda x: int(x["day_range"].split()[1].split("-")[0]))
    
    print(f"\nFinal itinerary ({len(unique_itinerary)} items):")
    for item in unique_itinerary:
        print(f"  {item['day_range']}: {item['place']}")

if __name__ == "__main__":
    test_gold_extraction() 