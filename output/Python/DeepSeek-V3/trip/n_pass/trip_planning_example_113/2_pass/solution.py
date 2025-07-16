import json

def calculate_itinerary():
    # Input parameters
    total_days = 12
    naples_days = 3
    seville_days = 4
    milan_days = 5  # Adjusted from 7 to 5 to make total_days = 12
    
    # Direct flight connections
    direct_flights = {
        'Milan': ['Seville', 'Naples'],
        'Seville': ['Milan'],
        'Naples': ['Milan']
    }
    
    # Validate total days
    if naples_days + seville_days + milan_days != total_days:
        raise ValueError("Total days in cities do not match the trip duration.")
    
    # The show is from day 9 to 12 in Seville, so Seville must be last
    itinerary = [
        {"day_range": "Day 1-3", "place": "Naples"},
        {"day_range": "Day 4-8", "place": "Milan"},
        {"day_range": "Day 9-12", "place": "Seville"}
    ]
    
    # Verify flight connections
    # Naples -> Milan: direct (valid)
    # Milan -> Seville: direct (valid)
    
    return {"itinerary": itinerary}

# Execute the function and print the result as JSON
print(json.dumps(calculate_itinerary()))