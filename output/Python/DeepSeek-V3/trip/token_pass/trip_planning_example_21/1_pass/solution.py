import json

def plan_trip():
    total_days = 10
    venice_days_needed = 6
    mykonos_days_needed = 2
    vienna_days_needed = 4
    
    # Direct flights: Mykonos <-> Vienna, Vienna <-> Venice
    # So route must be Mykonos -> Vienna -> Venice or reverse
    
    # We found one feasible schedule:
    # Day 1: Mykonos
    # Day 2: Travel Mykonos -> Vienna (counts for both)
    # Day 3-4: Vienna
    # Day 5: Travel Vienna -> Venice (counts for both)
    # Day 6-10: Venice
    
    itinerary = []
    itinerary.append({"day_range": "Day 1", "place": "Mykonos"})
    itinerary.append({"day_range": "Day 2", "place": "Mykonos → Vienna (travel)"})
    itinerary.append({"day_range": "Day 3-4", "place": "Vienna"})
    itinerary.append({"day_range": "Day 5", "place": "Vienna → Venice (travel)"})
    itinerary.append({"day_range": "Day 6-10", "place": "Venice"})
    
    # Verification
    days_count = {
        "Venice": 0,
        "Vienna": 0,
        "Mykonos": 0
    }
    
    # Simulate day by day
    day_plan = [
        ("Mykonos",),
        ("Mykonos", "Vienna"),
        ("Vienna",),
        ("Vienna",),
        ("Vienna", "Venice"),
        ("Venice",),
        ("Venice",),
        ("Venice",),
        ("Venice",),
        ("Venice",)
    ]
    
    for day in day_plan:
        for city in day:
            days_count[city] += 1
    
    # Check constraints
    assert days_count["Venice"] == venice_days_needed, f"Venice days mismatch: {days_count['Venice']}"
    assert days_count["Vienna"] == vienna_days_needed, f"Vienna days mismatch: {days_count['Vienna']}"
    assert days_count["Mykonos"] == mykonos_days_needed, f"Mykonos days mismatch: {days_count['Mykonos']}"
    assert sum(len(day) for day in day_plan) == total_days + 2  # 2 travel days double-counted
    
    # Workshop in Venice between day 5 and 10
    venice_days_indices = [i+1 for i, day in enumerate(day_plan) if "Venice" in day]
    assert any(5 <= d <= 10 for d in venice_days_indices), "Workshop constraint not met"
    
    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = plan_trip()
    print(json.dumps(result, indent=2))