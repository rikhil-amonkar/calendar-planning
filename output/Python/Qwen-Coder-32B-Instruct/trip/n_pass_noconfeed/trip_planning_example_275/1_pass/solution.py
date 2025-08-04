import json

def calculate_itinerary():
    # Define the constraints
    total_days = 14
    split_days = 5
    vilnius_days = 4
    santorini_days = 2
    madrid_days = 6
    conference_days = [13, 14]

    # Initialize the itinerary
    itinerary = []

    # Start in Vilnius for 4 days
    itinerary.append({"day_range": f"Day 1-{vilnius_days}", "place": "Vilnius"})

    # Fly to Split on day 5 and stay for 5 days
    itinerary.append({"day_range": f"Day {vilnius_days}-{vilnius_days + split_days - 1}", "place": "Split"})

    # Fly to Madrid on day 9 and stay for 6 days
    itinerary.append({"day_range": f"Day {vilnius_days + split_days - 1}-{vilnius_days + split_days + madrid_days - 2}", "place": "Madrid"})

    # Fly to Santorini on day 14 and stay for 2 days including the conference
    itinerary.append({"day_range": f"Day {vilnius_days + split_days + madrid_days - 2}-Day {total_days}", "place": "Santorini"})

    return {"itinerary": itinerary}

# Calculate and print the itinerary in JSON format
print(json.dumps(calculate_itinerary(), indent=4))