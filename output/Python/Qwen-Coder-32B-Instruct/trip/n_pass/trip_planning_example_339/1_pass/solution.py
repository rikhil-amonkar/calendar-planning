import json

def calculate_itinerary():
    # Define the constraints
    total_days = 17
    days_in_riga = 7
    wedding_days_in_riga = range(11, 18)  # Day 11 to Day 17
    days_in_budapest = 7
    days_in_paris = 4
    days_in_warsaw = 2
    warsaw_show_days = range(1, 3)  # Day 1 to Day 2

    # Initialize the itinerary
    itinerary = []

    # Start in Warsaw for the show
    itinerary.append({"day_range": f"Day 1-2", "place": "Warsaw"})

    # Move to Riga for the wedding
    itinerary.append({"day_range": f"Day 2-10", "place": "Riga"})

    # Stay in Riga for the wedding
    itinerary.append({"day_range": f"Day 11-17", "place": "Riga"})

    # Calculate remaining days after Riga
    remaining_days_after_riga = total_days - 17

    # Move to Budapest after Riga
    if remaining_days_after_riga >= days_in_budapest:
        itinerary.append({"day_range": f"Day 18-{18 + days_in_budapest - 1}", "place": "Budapest"})
        remaining_days_after_budapest = remaining_days_after_riga - days_in_budapest
    else:
        raise ValueError("Not enough days to accommodate all stays.")

    # Move to Paris after Budapest
    if remaining_days_after_budapest >= days_in_paris:
        itinerary.append({"day_range": f"Day {18 + days_in_budapest}-{18 + days_in_budapest + days_in_paris - 1}", "place": "Paris"})
    else:
        raise ValueError("Not enough days to accommodate all stays.")

    return {"itinerary": itinerary}

# Calculate and print the itinerary
print(json.dumps(calculate_itinerary()))