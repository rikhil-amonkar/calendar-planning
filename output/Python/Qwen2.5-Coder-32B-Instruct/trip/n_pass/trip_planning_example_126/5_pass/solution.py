import json

def calculate_itinerary():
    # Input variables
    total_days = 11
    seville_days = 5
    paris_days = 2
    krakow_days = 4
    
    # Initialize itinerary
    itinerary = []
    
    # Start with Krakow for the workshop
    itinerary.append({"day_range": f"Day 1-{krakow_days}", "place": "Krakow"})
    
    # Move to Paris after the workshop
    current_day = krakow_days + 1
    itinerary.append({"day_range": f"Day {current_day}-{current_day + paris_days - 1}", "place": "Paris"})
    current_day += paris_days
    
    # Move to Seville
    itinerary.append({"day_range": f"Day {current_day}-{current_day + seville_days - 1}", "place": "Seville"})
    current_day += seville_days
    
    # Ensure the total days match the specified total
    if current_day != total_days + 1:
        raise ValueError(f"Total days mismatch: expected {total_days}, got {current_day - 1}")
    
    # Return the final itinerary as JSON
    return json.dumps({"itinerary": itinerary})

# Output the result
print(calculate_itinerary())