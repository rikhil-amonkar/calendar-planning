import json

def calculate_itinerary():
    # Input variables
    total_days = 17
    days_in_riga = 7
    days_in_budapest = 7
    days_in_paris = 4
    days_in_warsaw = 2
    wedding_days = range(10, 17)  # Day 11 to Day 17 (0-indexed)
    show_days = range(0, 2)  # Day 1 to Day 2 (0-indexed)

    # Initialize itinerary
    itinerary = []

    # Start in Warsaw for the show
    itinerary.append({"day_range": f"Day {show_days.start + 1}-{show_days.stop}", "place": "Warsaw"})

    # Fly to Riga for the wedding
    itinerary.append({"day_range": f"Day {show_days.stop + 1}-{wedding_days.start}", "place": "Riga"})

    # Stay in Riga for the wedding
    itinerary.append({"day_range": f"Day {wedding_days.start + 1}-{wedding_days.stop + 1}", "place": "Riga"})

    # Calculate remaining days after Riga
    remaining_days_after_riga = total_days - (wedding_days.stop + 1)

    # Determine the next city based on remaining days
    if remaining_days_after_riga >= days_in_budapest:
        # Go to Budapest
        itinerary.append({"day_range": f"Day {wedding_days.stop + 2}-{wedding_days.stop + 2 + days_in_budapest}", "place": "Budapest"})
        remaining_days_after_budapest = remaining_days_after_riga - days_in_budapest

        # Determine if there are enough days left for Paris
        if remaining_days_after_budapest >= days_in_paris:
            # Go to Paris
            itinerary.append({"day_range": f"Day {wedding_days.stop + 3 + days_in_budapest}-{wedding_days.stop + 3 + days_in_budapest + days_in_paris}", "place": "Paris"})
    else:
        # Not enough days left for Budapest, go directly to Paris
        itinerary.append({"day_range": f"Day {wedding_days.stop + 2}-{wedding_days.stop + 2 + remaining_days_after_riga}", "place": "Paris"})

    return itinerary

# Calculate and print the itinerary in JSON format
itinerary = calculate_itinerary()
print(json.dumps({"itinerary": itinerary}))