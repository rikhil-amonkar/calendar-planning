import json

def generate_itinerary():
    # Define the constraints
    madrid_days = range(1, 8)  # Day 1-7
    paris_days = range(8, 13)  # Day 8-12
    seville_day = 13  # Day 13
    bucharest_days = range(14, 16)  # Day 14-15

    # Create the itinerary
    itinerary = [
        {"day_range": f"Day {madrid_days.start}-{madrid_days.stop - 1}", "place": "Madrid"},
        {"day_range": f"Day {paris_days.start}-{paris_days.stop - 1}", "place": "Paris"},
        {"day_range": f"Day {seville_day}-{seville_day}", "place": "Seville"},
        {"day_range": f"Day {bucharest_days.start}-{bucharest_days.stop - 1}", "place": "Bucharest"}
    ]

    return json.dumps({"itinerary": itinerary}, indent=4)

# Generate and print the itinerary
print(generate_itinerary())