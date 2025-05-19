import json

def calculate_itinerary():
    total_days = 10
    venice_days = 6
    mykonos_days = 2
    vienna_days = 4
    workshop_start = 5
    workshop_end = 10

    itinerary = []
    
    # Mykonos: Days 1-2 (2 days)
    mykonos_end = 1 + mykonos_days - 1
    itinerary.append({"day_range": f"Day 1-{mykonos_end}", "place": "Mykonos"})
    
    # Vienna starts on transition day (Day 2)
    vienna_start = mykonos_end
    vienna_end = vienna_start + vienna_days - 1
    itinerary.append({"day_range": f"Day {vienna_start}-{vienna_end}", "place": "Vienna"})
    
    # Venice starts on transition day (Day 5)
    venice_start = vienna_end
    venice_end = venice_start + venice_days - 1
    itinerary.append({"day_range": f"Day {venice_start}-{venice_end}", "place": "Venice"})
    
    # Validate workshop days are within Venice stay
    if not (venice_start <= workshop_start and venice_end >= workshop_end):
        raise ValueError("Workshop days not covered in Venice itinerary")
    
    # Ensure total days match
    if venice_end != total_days:
        raise ValueError("Total itinerary days do not sum to 10")
    
    return {"itinerary": itinerary}

print(json.dumps(calculate_itinerary()))