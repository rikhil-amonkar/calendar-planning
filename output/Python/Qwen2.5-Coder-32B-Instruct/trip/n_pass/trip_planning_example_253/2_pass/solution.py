import json

def calculate_itinerary():
    # Define the constraints
    total_days = 14
    amsterdam_days = 3
    amsterdam_workshop_days = range(9, 12)  # Day 9 to Day 11
    vienna_days = 7
    santorini_days = 4
    lyon_days = 3
    lyon_wedding_days = range(7, 10)  # Day 7 to Day 9

    # Initialize the itinerary
    itinerary = []

    # Start in Vienna for the first 7 days
    current_city = 'Vienna'
    current_day = 1
    itinerary.append({"day_range": f"Day {current_day}-{current_day + vienna_days - 1}", "place": current_city})
    current_day += vienna_days

    # Fly to Lyon for the wedding
    current_city = 'Lyon'
    itinerary.append({"day_range": f"Day {current_day}-{current_day + lyon_days - 1}", "place": current_city})
    current_day += lyon_days

    # Fly to Amsterdam for the workshop
    current_city = 'Amsterdam'
    itinerary.append({"day_range": f"Day {current_day}-{current_day + amsterdam_days - 1}", "place": current_city})
    current_day += amsterdam_days

    # Fly to Santorini for the remaining days
    current_city = 'Santorini'
    itinerary.append({"day_range": f"Day {current_day}-{total_days}", "place": current_city})

    return {"itinerary": itinerary}

# Calculate and print the itinerary
print(json.dumps(calculate_itinerary()))