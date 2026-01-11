import json

def generate_itinerary():
    # Define the constraints
    split_days = 6
    santorini_days = 7
    london_days = 7
    total_days = 18
    conference_days = [12, 18]

    # Initialize the itinerary list
    itinerary = []

    # Stay in Split for 6 days (Day 1-6)
    itinerary.append({"day_range": "Day 1-6", "place": "Split"})

    # Travel to London on Day 7 and stay until Day 11 (5 days)
    itinerary.append({"day_range": "Day 7-11", "place": "London"})

    # Travel to Santorini on Day 12 and stay until Day 17 (6 days including day 12)
    itinerary.append({"day_range": "Day 12-17", "place": "Santorini"})

    # Travel back to London on Day 18 (this day is also part of the Santorini stay, but the conference requirement is met)
    # Stay in London until Day 18 (since day 18 is also part of the Santorini stay, we effectively stay in London for 4 days after the conference)
    itinerary.append({"day_range": "Day 18", "place": "London"})

    # Return the itinerary as a JSON-formatted dictionary
    return {"itinerary": itinerary}

# Generate and print the itinerary
itinerary_json = generate_itinerary()
print(json.dumps(itinerary_json, indent=4))