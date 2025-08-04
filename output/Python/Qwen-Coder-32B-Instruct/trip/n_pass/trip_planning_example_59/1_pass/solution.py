import json

def calculate_itinerary():
    # Input variables
    total_days = 16
    stay_lyon = 7
    stay_bucharest = 7
    stay_porto = 4
    wedding_days = range(1, 8)  # Days 1 to 7 inclusive

    # Initialize itinerary
    itinerary = []

    # Start in Bucharest for the wedding
    itinerary.append({"day_range": f"Day 1-{stay_bucharest}", "place": "Bucharest"})

    # Transition from Bucharest to Lyon (day 7 to 8)
    itinerary.append({"day_range": f"Day {stay_bucharest}-{stay_bucharest + 1}", "place": "Lyon"})

    # Stay in Lyon for the remaining days (day 8 to 14)
    itinerary.append({"day_range": f"Day {stay_bucharest + 1}-{stay_bucharest + stay_lyon}", "place": "Lyon"})

    # Transition from Lyon to Porto (day 14 to 15)
    itinerary.append({"day_range": f"Day {stay_bucharest + stay_lyon}-{stay_bucharest + stay_lyon + 1}", "place": "Porto"})

    # Stay in Porto for the remaining days (day 15 to 18)
    itinerary.append({"day_range": f"Day {stay_bucharest + stay_lyon + 1}-{total_days}", "place": "Porto"})

    return {"itinerary": itinerary}

# Calculate and print the itinerary in JSON format
print(json.dumps(calculate_itinerary(), indent=4))