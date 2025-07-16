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
    current_day = 1
    itinerary = []
    
    # Naples first
    end_day = current_day + naples_days - 1
    itinerary.append({"day_range": f"Day {current_day}-{end_day}", "place": "Naples"})
    current_day = end_day + 1
    
    # Then Milan
    end_day = current_day + milan_days - 1
    itinerary.append({"day_range": f"Day {current_day}-{end_day}", "place": "Milan"})
    current_day = end_day + 1
    
    # Finally Seville
    end_day = current_day + seville_days - 1
    itinerary.append({"day_range": f"Day {current_day}-{end_day}", "place": "Seville"})
    
    # Verify flight connections
    if len(itinerary) > 1:
        for i in range(len(itinerary)-1):
            current_city = itinerary[i]["place"]
            next_city = itinerary[i+1]["place"]
            if next_city not in direct_flights[current_city]:
                raise ValueError(f"No direct flight from {current_city} to {next_city}")
    
    return {"itinerary": itinerary}

# Execute the function and print the result as JSON
print(json.dumps(calculate_itinerary()))