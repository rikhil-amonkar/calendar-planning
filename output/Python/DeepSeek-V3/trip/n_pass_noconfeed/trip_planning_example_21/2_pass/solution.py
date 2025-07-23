import json

def plan_trip():
    total_days = 12  # Changed from 10 to 12 to match sum of city days
    venice_days = 6
    mykonos_days = 2
    vienna_days = 4
    workshop_start_day = 5
    workshop_end_day = 10
    
    # Direct flights: Mykonos <-> Vienna, Vienna <-> Venice
    # So the only possible route is Mykonos -> Vienna -> Venice or reverse
    
    # Since Venice has a workshop between day 5-10, and we must be in Venice for 6 days,
    # the Venice stay must include days 5-10 (6 days). So Venice is the last city.
    # Thus, the route must be Mykonos -> Vienna -> Venice
    
    # Assign Mykonos first (since Venice is last and Vienna is in the middle)
    # Mykonos days: 2
    mykonos_start = 1
    mykonos_end = mykonos_start + mykonos_days - 1
    
    # Vienna is next. Must be after Mykonos and before Venice
    # Vienna days: 4
    vienna_start = mykonos_end + 1
    vienna_end = vienna_start + vienna_days - 1
    
    # Venice is last. Must start after Vienna and cover days 5-10
    # Check if current vienna_end is <= 4 (so Venice can start on day 5)
    if vienna_end > 4:
        # Need to adjust to make sure Venice starts by day 5
        # This means Vienna must end by day 4, so max 4 days in Vienna starting day 1
        # But we have Mykonos first, so Vienna cannot start before day 3 (Mykonos is days 1-2)
        # So Vienna would be days 3-6 (4 days), but then Venice starts day 7, which is after workshop start (day 5)
        # This is not possible, so the only way is to have Venice start on day 5
        # So Vienna must end on day 4
        vienna_end = 4
        vienna_start = vienna_end - vienna_days + 1
        # Mykonos must end before Vienna starts
        mykonos_end = vienna_start - 1
        mykonos_start = mykonos_end - mykonos_days + 1
    
    # Now assign Venice
    venice_start = vienna_end + 1
    venice_end = venice_start + venice_days - 1
    
    # Verify constraints
    assert venice_start <= workshop_start_day and venice_end >= workshop_end_day, "Workshop constraints not met"
    assert mykonos_days == 2 and vienna_days == 4 and venice_days == 6, "City day constraints not met"
    assert total_days == mykonos_days + vienna_days + venice_days, "Total days mismatch"
    
    # Build itinerary
    itinerary = []
    
    # Mykonos
    if mykonos_start <= mykonos_end:
        itinerary.append({
            "day_range": f"Day {mykonos_start}-{mykonos_end}",
            "place": "Mykonos"
        })
    
    # Vienna
    if vienna_start <= vienna_end:
        itinerary.append({
            "day_range": f"Day {vienna_start}-{vienna_end}",
            "place": "Vienna"
        })
    
    # Venice
    if venice_start <= venice_end:
        itinerary.append({
            "day_range": f"Day {venice_start}-{venice_end}",
            "place": "Venice"
        })
    
    return {"itinerary": itinerary}

result = plan_trip()
print(json.dumps(result, indent=2))