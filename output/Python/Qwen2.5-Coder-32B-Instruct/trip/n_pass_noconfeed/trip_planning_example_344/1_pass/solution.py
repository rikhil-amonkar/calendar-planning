import json

def calculate_itinerary():
    # Input constraints
    total_days = 20
    valencia_stay = 6
    athens_stay = 6
    naples_stay = 5
    zurich_stay = 6
    athens_visit_days = (1, 6)
    naples_wedding_days = (16, 20)

    # Initialize variables
    itinerary = []
    current_day = 1

    # Start in Athens for the first 6 days
    itinerary.append({"day_range": f"Day {current_day}-{current_day + athens_stay - 1}", "place": "Athens"})
    current_day += athens_stay

    # Move to Valencia next (since we need to stay there for 6 days and it's connected to Athens)
    itinerary.append({"day_range": f"Day {current_day}-{current_day + valencia_stay - 1}", "place": "Valencia"})
    current_day += valencia_stay

    # Move to Naples for 5 days (connected to Valencia and needs to be before the wedding)
    itinerary.append({"day_range": f"Day {current_day}-{current_day + naples_stay - 1}", "place": "Naples"})
    current_day += naples_stay

    # Move to Zurich for the remaining days (connected to Naples)
    remaining_days = total_days - current_day + 1
    itinerary.append({"day_range": f"Day {current_day}-{current_day + remaining_days - 1}", "place": "Zurich"})

    return itinerary

# Calculate and print the itinerary in JSON format
itinerary = calculate_itinerary()
print(json.dumps({"itinerary": itinerary}))