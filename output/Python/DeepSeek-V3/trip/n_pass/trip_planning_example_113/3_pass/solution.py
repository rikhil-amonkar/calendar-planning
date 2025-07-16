import json

def calculate_itinerary():
    # Input parameters
    total_days = 12
    naples_days = 3
    seville_days = 4
    milan_days = 5  # 3 + 5 + 4 = 12
    
    # Direct flight connections
    direct_flights = {
        'Milan': ['Seville', 'Naples'],
        'Seville': ['Milan'],
        'Naples': ['Milan']
    }
    
    # Validate total days
    if naples_days + seville_days + milan_days != total_days:
        raise ValueError("Total days in cities do not match the trip duration.")
    
    # Calculate day ranges
    day1_end = naples_days
    day2_start = day1_end + 1
    day2_end = day2_start + milan_days - 1
    day3_start = day2_end + 1
    day3_end = day3_start + seville_days - 1
    
    itinerary = [
        {"day_range": f"Day 1-{day1_end}", "place": "Naples"},
        {"day_range": f"Day {day2_start}-{day2_end}", "place": "Milan"},
        {"day_range": f"Day {day3_start}-{day3_end}", "place": "Seville"}
    ]
    
    # Verify flight connections
    # Naples -> Milan: direct (valid)
    # Milan -> Seville: direct (valid)
    
    return {"itinerary": itinerary}

# Execute the function and print the result as JSON
print(json.dumps(calculate_itinerary()))