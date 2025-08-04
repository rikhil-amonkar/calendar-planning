import json

def calculate_itinerary():
    # Define the constraints
    total_days = 17
    days_in_warsaw = 2  # Day 1 to Day 2
    days_in_riga = 10   # Day 3 to Day 12 (before and during the wedding)
    days_in_budapest = 3  # Day 13 to Day 15
    days_in_paris = 2   # Day 16 to Day 17

    # Initialize the itinerary
    itinerary = []

    # Start in Warsaw for the show
    itinerary.append({"day_range": f"Day 1-{days_in_warsaw}", "place": "Warsaw"})

    # Move to Riga before and during the wedding
    itinerary.append({"day_range": f"Day {days_in_warsaw + 1}-{days_in_warsaw + days_in_riga}", "place": "Riga"})

    # Move to Budapest after Riga
    itinerary.append({"day_range": f"Day {days_in_warsaw + days_in_riga + 1}-{days_in_warsaw + days_in_riga + days_in_budapest}", "place": "Budapest"})

    # Move to Paris after Budapest
    itinerary.append({"day_range": f"Day {days_in_warsaw + days_in_riga + days_in_budapest + 1}-{total_days}", "place": "Paris"})

    return {"itinerary": itinerary}

# Calculate and print the itinerary
print(json.dumps(calculate_itinerary(), indent=2))