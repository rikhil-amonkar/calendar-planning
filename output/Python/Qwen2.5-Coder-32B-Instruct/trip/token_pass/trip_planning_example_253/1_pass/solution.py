import json

def calculate_itinerary():
    # Define the constraints
    total_days = 14
    days_in_amsterdam = 3
    days_in_vienna = 7
    days_in_santorini = 4
    days_in_lyon = 3
    amsterdam_workshop_days = (9, 11)  # Inclusive
    lyon_wedding_days = (7, 9)  # Inclusive

    # Initialize the itinerary
    itinerary = []

    # Start with Vienna since it has the longest stay
    itinerary.append({"day_range": f"Day 1-{days_in_vienna}", "place": "Vienna"})
    
    # Next, place Lyon for the wedding
    itinerary.append({"day_range": f"Day {lyon_wedding_days[0]}-{lyon_wedding_days[1]}", "place": "Lyon"})
    
    # Then, place Amsterdam for the workshop
    itinerary.append({"day_range": f"Day {amsterdam_workshop_days[0]}-{amsterdam_workshop_days[1]}", "place": "Amsterdam"})
    
    # Finally, place Santorini
    start_day_santorini = amsterdam_workshop_days[1] + 1
    end_day_santorini = start_day_santorini + days_in_santorini - 1
    itinerary.append({"day_range": f"Day {start_day_santorini}-{end_day_santorini}", "place": "Santorini"})
    
    # Verify the total days
    assert end_day_santorini == total_days, "The itinerary does not cover exactly 14 days"
    
    return {"itinerary": itinerary}

# Calculate and print the itinerary
itinerary_result = calculate_itinerary()
print(json.dumps(itinerary_result, indent=4))