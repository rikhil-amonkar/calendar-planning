import json

def calculate_itinerary():
    # Define the constraints
    total_days = 14
    amsterdam_days = 3
    amsterdam_workshop_days = range(11, 14)  # Day 11 to Day 13
    vienna_days = 7
    santorini_days = 1
    lyon_days = 3
    lyon_wedding_days = range(8, 11)  # Day 8 to Day 10

    # Initialize the itinerary
    itinerary = []

    # Start in Vienna for the first 7 days
    current_city = 'Vienna'
    current_day = 1
    itinerary.append({"day_range": f"Day {current_day}-{current_day + vienna_days - 1}", "place": current_city})
    current_day += vienna_days

    # Fly to Lyon for the wedding on Day 8-10
    current_city = 'Lyon'
    itinerary.append({"day_range": f"Day {current_day}-{current_day + lyon_days - 1}", "place": current_city})
    current_day += lyon_days

    # Fly to Amsterdam for the workshop on Day 11-13
    current_city = 'Amsterdam'
    itinerary.append({"day_range": f"Day {current_day}-{current_day + amsterdam_days - 1}", "place": current_city})
    current_day += amsterdam_days

    # Fly to Santorini for the remaining day (Day 14)
    current_city = 'Santorini'
    itinerary.append({"day_range": f"Day {total_days}-{total_days}", "place": current_city})

    return {"itinerary": itinerary}

# Calculate and print the itinerary
print(json.dumps(calculate_itinerary(), indent=4))