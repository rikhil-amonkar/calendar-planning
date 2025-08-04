import json

def calculate_itinerary():
    # Input variables
    total_days = 11
    seville_days = 6
    paris_days = 2
    krakow_days = 5
    krakow_workshop_days = range(1, 6)
    
    # Initialize itinerary
    itinerary = []
    
    # Start with Krakow for the workshop
    itinerary.append({"day_range": f"Day {krakow_workshop_days.start}-{krakow_workshop_days.stop}", "place": "Krakow"})
    
    # Move to Paris after the workshop
    current_day = krakow_workshop_days.stop
    itinerary.append({"day_range": f"Day {current_day}-{current_day + paris_days - 1}", "place": "Paris"})
    current_day += paris_days
    
    # Move to Seville
    itinerary.append({"day_range": f"Day {current_day}-{current_day + seville_days - 1}", "place": "Seville"})
    current_day += seville_days
    
    # Return the final itinerary as JSON
    return json.dumps({"itinerary": itinerary})

# Output the result
print(calculate_itinerary())