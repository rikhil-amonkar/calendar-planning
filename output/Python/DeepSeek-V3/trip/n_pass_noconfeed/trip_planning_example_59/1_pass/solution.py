import json

def plan_trip():
    total_days = 16
    lyon_days = 7
    bucharest_days = 7
    porto_days = 4
    
    # Since the wedding is between day 1 and 7, Bucharest must include day 1-7
    # So Bucharest is the starting city
    itinerary = []
    
    # Bucharest: Day 1-7 (7 days)
    itinerary.append({"day_range": "Day 1-7", "place": "Bucharest"})
    
    # Next city must be Lyon (only direct flight from Bucharest)
    # Transition day is day 7 (spend day 7 in both Bucharest and Lyon)
    remaining_lyon_days = lyon_days - 1  # day 7 counts as 1 day in Lyon
    
    # Lyon: Day 7-14 (7 days: day 7-13 is 7 days, but day 7 is transition)
    # So day 7-13 is 7 days in Lyon (including transition day)
    itinerary.append({"day_range": "Day 7-14", "place": "Lyon"})
    
    # Next city must be Porto (only direct flight from Lyon)
    # Transition day is day 14 (spend day 14 in both Lyon and Porto)
    remaining_porto_days = porto_days - 1  # day 14 counts as 1 day in Porto
    
    # Porto: Day 14-17 (4 days: day 14-17 is 4 days, but we only have 16 days)
    # So day 14-16 is 3 days in Porto (including transition day)
    # But we need 4 days in Porto, so adjust Lyon to end on day 13
    # Recalculate:
    
    # Correct calculation:
    # Bucharest: Day 1-7 (7 days)
    # Lyon: Day 7-13 (7 days: day 7 is transition, day 8-13 is 6 days, total 7)
    # Porto: Day 13-16 (4 days: day 13 is transition, day 14-16 is 3 days, total 4)
    
    itinerary = [
        {"day_range": "Day 1-7", "place": "Bucharest"},
        {"day_range": "Day 7-13", "place": "Lyon"},
        {"day_range": "Day 13-16", "place": "Porto"}
    ]
    
    return {"itinerary": itinerary}

result = plan_trip()
print(json.dumps(result, indent=2))