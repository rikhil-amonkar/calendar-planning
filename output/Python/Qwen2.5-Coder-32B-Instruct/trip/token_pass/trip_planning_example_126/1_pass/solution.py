import json

def calculate_itinerary():
    # Define the constraints
    total_days = 11
    seville_days = 6
    paris_days = 2
    krakow_days = 5
    krakow_workshop_start = 1
    krakow_workshop_end = 5
    
    # Initialize the itinerary list
    itinerary = []
    
    # Add Krakow stay (including workshop)
    itinerary.append({"day_range": f"Day {krakow_workshop_start}-{krakow_workshop_end}", "place": "Krakow"})
    
    # Add travel day from Krakow to Paris
    current_day = krakow_workshop_end + 1
    itinerary.append({"day_range": f"Day {current_day}", "place": "Travel (Krakow to Paris)"})
    current_day += 1
    
    # Add Paris stay
    paris_stay_end = current_day + paris_days - 1
    itinerary.append({"day_range": f"Day {current_day}-{paris_stay_end}", "place": "Paris"})
    current_day = paris_stay_end + 1
    
    # Add travel day from Paris to Seville
    itinerary.append({"day_range": f"Day {current_day}", "place": "Travel (Paris to Seville)"})
    current_day += 1
    
    # Add Seville stay
    seville_stay_end = current_day + seville_days - 1
    seville_stay_end = min(seville_stay_end, total_days)  # Ensure we don't exceed total days
    itinerary.append({"day_range": f"Day {current_day}-{seville_stay_end}", "place": "Seville"})
    
    # Return the itinerary as a JSON-formatted dictionary
    return {"itinerary": itinerary}

# Calculate and print the itinerary
itinerary_json = calculate_itinerary()
print(json.dumps(itinerary_json, indent=4))