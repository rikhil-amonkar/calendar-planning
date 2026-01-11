import json

def calculate_itinerary():
    # Initialize the itinerary list
    itinerary = []

    # Day 1-2: Workshop in Prague
    itinerary.append({"day_range": "Day 1-2", "place": "Prague"})

    # Day 2-5: Annual show in Helsinki (overlap with Prague on Day 2)
    itinerary.append({"day_range": "Day 2-5", "place": "Helsinki"})

    # Day 5-8: Stay in Helsinki (since we already spent 2 days in Helsinki, we need 2 more days)
    itinerary.append({"day_range": "Day 5-8", "place": "Helsinki"})

    # Day 8-10: Move to Frankfurt (direct flight from Helsinki)
    itinerary.append({"day_range": "Day 8-10", "place": "Frankfurt"})

    # Day 10-12: Move to Naples (direct flight from Frankfurt)
    itinerary.append({"day_range": "Day 10-12", "place": "Naples"})

    # Day 12-14: Move to Lyon (direct flight from Naples) but since we only have 12 days, we need to adjust
    # Instead, we can extend Frankfurt stay or Naples stay or add Lyon in the middle
    # Adjusting Frankfurt stay to 5 days and Naples stay to 6 days
    # But since we need exact 12 days, let's adjust the previous steps

    # Corrected Itinerary
    # Day 1-2: Workshop in Prague
    itinerary[0] = {"day_range": "Day 1-2", "place": "Prague"}

    # Day 2-5: Annual show in Helsinki (overlap with Prague on Day 2)
    itinerary[1] = {"day_range": "Day 2-5", "place": "Helsinki"}

    # Day 5-8: Stay in Helsinki (since we already spent 2 days in Helsinki, we need 2 more days)
    itinerary[2] = {"day_range": "Day 5-8", "place": "Helsinki"}

    # Day 8-11: Move to Frankfurt (direct flight from Helsinki)
    itinerary[3] = {"day_range": "Day 8-11", "place": "Frankfurt"}

    # Day 11-12: Move to Naples (direct flight from Frankfurt)
    itinerary[4] = {"day_range": "Day 11-12", "place": "Naples"}

    # Day 9-11: Move to Lyon (direct flight from Helsinki)
    itinerary.insert(3, {"day_range": "Day 9-11", "place": "Lyon"})

    # Adjust Frankfurt stay to 3 days
    itinerary[3] = {"day_range": "Day 11-12", "place": "Frankfurt"}

    # Final Itinerary
    final_itinerary = {"itinerary": itinerary}

    return final_itinerary

# Calculate and print the itinerary
itinerary_json = calculate_itinerary()
print(json.dumps(itinerary_json, indent=4))