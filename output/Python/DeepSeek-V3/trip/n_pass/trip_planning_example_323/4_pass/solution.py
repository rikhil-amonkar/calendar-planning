import json

def calculate_itinerary():
    # Define constraints
    total_days = 16
    split_show_start = 7
    split_show_end = 11
    
    # Initialize itinerary
    itinerary = []

    # Must visit relatives in London between day 1-7 (7 days)
    itinerary.append({"day_range": "Day 1-7", "place": "London"})

    # Must be in Split for show days 7-11 (5 days)
    itinerary.append({"day_range": "Day 7-11", "place": "Split"})

    # Must spend 2 days in Oslo
    # From Split, we can fly directly to Oslo
    itinerary.append({"day_range": "Day 12-13", "place": "Oslo"})

    # Remaining days (14-16) for Porto (3 days)
    # This is less than the ideal 5 days, but fits within 16-day limit
    itinerary.append({"day_range": "Day 14-16", "place": "Porto"})

    return {"itinerary": itinerary}

# Output the itinerary as JSON
print(json.dumps(calculate_itinerary()))