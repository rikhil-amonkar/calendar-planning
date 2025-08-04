import json

def calculate_itinerary():
    # Define the constraints
    total_days = 17
    days_in_warsaw = 2  # Day 1 to Day 2
    days_in_riga_before_wedding = 5  # Day 3 to Day 7
    days_in_riga_during_wedding = 5  # Day 8 to Day 12
    days_in_budapest = 3  # Day 13 to Day 15
    days_in_paris = 2  # Day 16 to Day 17

    # Initialize the itinerary
    itinerary = []

    # Start in Warsaw for the show
    itinerary.append({"day_range": f"Day 1-2", "place": "Warsaw"})

    # Move to Riga before the wedding
    itinerary.append({"day_range": f"Day 3-7", "place": "Riga"})

    # Stay in Riga for the wedding
    itinerary.append({"day_range": f"Day 8-12", "place": "Riga"})

    # Move to Budapest after Riga
    itinerary.append({"day_range": f"Day 13-15", "place": "Budapest"})

    # Move to Paris after Budapest
    itinerary.append({"day_range": f"Day 16-17", "place": "Paris"})

    return {"itinerary": itinerary}

# Calculate and print the itinerary
print(json.dumps(calculate_itinerary(), indent=2))