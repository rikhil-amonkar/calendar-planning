import json

def generate_itinerary():
    # Define the constraints
    days_in_naples = 3
    days_in_seville = 4
    event_days_in_seville = (9, 12)  # inclusive
    days_in_milan = 7

    # Initialize the itinerary list
    itinerary = []

    # Start in Naples for 3 days (Day 1-3)
    itinerary.append({"day_range": "Day 1-3", "place": "Naples"})

    # Fly to Milan on Day 4 and stay for 3 more days (Day 4-6)
    itinerary.append({"day_range": "Day 4-6", "place": "Milan"})

    # Fly to Seville on Day 6 and stay until Day 12 (inclusive)
    itinerary.append({"day_range": "Day 6-12", "place": "Seville"})

    # Stay in Milan for the remaining 2 days (Day 13 and 14 are not needed)
    itinerary.append({"day_range": "Day 12-12", "place": "Milan"})

    # Construct the final JSON output
    result = {"itinerary": itinerary}

    return json.dumps(result, indent=4)

# Generate and print the itinerary
print(generate_itinerary())