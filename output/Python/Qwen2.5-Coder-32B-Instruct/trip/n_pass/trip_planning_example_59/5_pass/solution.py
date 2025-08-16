import json

def calculate_itinerary():
    # Input variables
    total_days = 16
    stay_lyon = 7
    stay_bucharest = 7
    stay_porto = 2  # Adjusted to fit within the total days after removing unnecessary overlap

    # Initialize itinerary
    itinerary = []

    # Start in Bucharest for the first 7 days
    itinerary.append({"day_range": f"1-{stay_bucharest}", "place": "Bucharest"})

    # Stay in Lyon for the next 7 days (days 8 to 14)
    itinerary.append({"day_range": f"{stay_bucharest + 1}-{stay_bucharest + stay_lyon}", "place": "Lyon"})

    # Stay in Porto for the remaining days (days 15 to 16)
    itinerary.append({"day_range": f"{stay_bucharest + stay_lyon + 1}-{total_days}", "place": "Porto"})

    return {"itinerary": itinerary}

# Calculate and print the itinerary in JSON format
print(json.dumps(calculate_itinerary(), indent=4))