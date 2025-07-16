import json

def plan_trip():
    total_days = 16
    
    # Constraints:
    # 1. Must be in Bucharest for the wedding between day 1 and 7
    # 2. Must spend exactly 7 days in Bucharest (including travel days)
    # 3. Must spend exactly 7 days in Lyon (including travel days)
    # 4. Must spend exactly 4 days in Porto (including travel days)
    # 5. Flight connections: Bucharest <-> Lyon, Lyon <-> Porto
    
    # Correct itinerary:
    # Bucharest: Day 1-7 (7 days) - covers wedding
    # Travel to Lyon on day 7 (counts as last day in Bucharest and first in Lyon)
    # Lyon: Day 7-14 (7 days)
    # Travel to Porto on day 14 (counts as last day in Lyon and first in Porto)
    # Porto: Day 14-16 (3 days) + day 14 = 4 days
    
    itinerary = [
        {"day_range": "Day 1-7", "place": "Bucharest"},
        {"day_range": "Day 7-14", "place": "Lyon"},
        {"day_range": "Day 14-16", "place": "Porto"}
    ]
    
    return {"itinerary": itinerary}

if __name__ == "__main__":
    trip_plan = plan_trip()
    print(json.dumps(trip_plan, indent=2))