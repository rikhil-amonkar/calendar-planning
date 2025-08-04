import json

def calculate_itinerary():
    # Input constraints
    total_days = 11
    seville_days = 6
    paris_days = 2
    krakow_days = 5
    krakow_workshop_start = 1
    krakow_workshop_end = 5
    
    # Initialize itinerary
    itinerary = []
    
    # Stay in Krakow for the workshop period
    itinerary.append({"day_range": f"Day {krakow_workshop_start}-{krakow_workshop_end}", "place": "Krakow"})
    
    # Calculate remaining days after the workshop in Krakow
    remaining_days_after_krakow = krakow_days - (krakow_workshop_end - krakow_workshop_start + 1)
    
    # If there are remaining days in Krakow, add them to the itinerary
    if remaining_days_after_krakow > 0:
        next_day = krakow_workshop_end + 1
        last_day_in_krakow = next_day + remaining_days_after_krakow - 1
        itinerary.append({"day_range": f"Day {next_day}-{last_day_in_krakow}", "place": "Krakow"})
        next_day = last_day_in_krakow + 1
    else:
        next_day = krakow_workshop_end + 1
    
    # Fly to Paris and stay there
    itinerary.append({"day_range": f"Day {next_day}-{next_day + paris_days - 1}", "place": "Paris"})
    next_day += paris_days
    
    # Fly to Seville and stay there
    itinerary.append({"day_range": f"Day {next_day}-{next_day + seville_days - 1}", "place": "Seville"})
    
    # Output the itinerary as JSON
    return json.dumps({"itinerary": itinerary})

# Run the function and print the result
print(calculate_itinerary())