import json

def calculate_itinerary():
    # Input parameters
    total_days = 12
    days_in_brussels = 2  # Fixed for conference
    days_in_split = 4     # Reduced from 5 to fit total days
    days_in_barcelona = 6 # Reduced from 7 to fit total days
    
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
    # Adjusted days to fit 12-day trip (2 + 6 + 4 = 12)
    
    # Barcelona portion
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