import json

def calculate_itinerary():
    # Input parameters
    total_days = 12
    days_in_brussels = 2
    days_in_split = 5
    days_in_barcelona = 7
    
    # Flight connections
    connections = {
        'Brussels': ['Barcelona'],
        'Barcelona': ['Brussels', 'Split'],
        'Split': ['Barcelona']
    }
    
    # Validate total days
    total_requested = days_in_brussels + days_in_split + days_in_barcelona
    if total_requested != total_days:
        raise ValueError("Total days in cities do not match the trip duration.")
    
    # Conference days are fixed in Brussels (Day 1-2)
    itinerary = []
    current_day = 1
    
    # Brussels (Day 1-2)
    itinerary.append({
        "day_range": f"Day {current_day}-{current_day + days_in_brussels - 1}",
        "place": "Brussels"
    })
    current_day += days_in_brussels
    
    # Next city must be Barcelona (only direct flight from Brussels)
    # From Barcelona, can go to Split
    # We need to spend 7 days in Barcelona and 5 in Split
    # Since we have 10 days left (12 - 2), and 7 + 5 = 12, but we have 10, we need overlap
    
    # Option 1: Barcelona first, then Split
    # Days in Barcelona: 7 (includes flight day from Brussels)
    # Days in Split: 5 (includes flight day from Barcelona)
    # But total would be 2 (Brussels) + 6 (Barcelona) + 4 (Split) = 12 (since flight days count for both)
    
    # Calculate overlapping days
    # Days in Barcelona includes the arrival day from Brussels (Day 3)
    barcelona_start = current_day
    barcelona_end = barcelona_start + days_in_barcelona - 1
    
    # Flight to Split is on the last day in Barcelona (barcelona_end)
    split_start = barcelona_end
    split_end = split_start + days_in_split - 1
    
    if split_end > total_days:
        raise ValueError("Invalid itinerary: exceeds total days.")
    
    itinerary.append({
        "day_range": f"Day {barcelona_start}-{barcelona_end}",
        "place": "Barcelona"
    })
    itinerary.append({
        "day_range": f"Day {split_start}-{split_end}",
        "place": "Split"
    })
    
    # Verify the itinerary
    calculated_days = {
        'Brussels': days_in_brussels,
        'Barcelona': days_in_barcelona,
        'Split': days_in_split
    }
    
    return {"itinerary": itinerary}

# Execute and print the result
result = calculate_itinerary()
print(json.dumps(result, indent=2))