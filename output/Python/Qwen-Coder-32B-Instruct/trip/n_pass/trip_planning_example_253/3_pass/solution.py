import json

def calculate_itinerary():
    # Define the constraints
    total_days = 14
    amsterdam_days = 3
    amsterdam_workshop_days = range(9, 12)  # Day 9 to Day 11
    vienna_days = 7
    santorini_days = 1
    lyon_days = 3
    lyon_wedding_days = range(7, 10)  # Day 7 to Day 9

    # Initialize the itinerary
    itinerary = []

    # Start in Vienna for the first 7 days
    current_city = 'Vienna'
    current_day = 1
    itinerary.append({"day_range": f"Day {current_day}-{current_day + vienna_days - 1}", "place": current_city})
    current_day += vienna_days

    # Fly to Lyon for the wedding on Day 7-9
    current_city = 'Lyon'
    itinerary.append({"day_range": f"Day {current_day}-{current_day + lyon_days - 1}", "place": current_city})
    current_day += lyon_days

    # Fly to Amsterdam for the workshop on Day 9-11
    # Note: This overlaps with the Lyon stay, so we need to adjust the Amsterdam start day
    current_city = 'Amsterdam'
    # Adjust the start day of Amsterdam to be after the Lyon wedding
    current_day = 9  # Start from Day 9
    itinerary.append({"day_range": f"Day {current_day}-{current_day + amsterdam_days - 1}", "place": current_city})
    current_day += amsterdam_days

    # Fly to Santorini for the remaining day (Day 14)
    current_city = 'Santorini'
    itinerary.append({"day_range": f"Day {total_days}-{total_days}", "place": current_city})

    return {"itinerary": itinerary}

# Calculate and print the itinerary
print(json.dumps(calculate_itinerary(), indent=4))