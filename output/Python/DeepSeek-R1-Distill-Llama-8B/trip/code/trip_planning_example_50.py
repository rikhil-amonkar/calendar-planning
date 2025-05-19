import json

def compute_itinerary():
    cities = {
        "Vilnius": {"days": 4},
        "Munich": {"days": 3},
        "Mykonos": {"days": 7}
    }

    flights = {
        "Vilnius": ["Munich"],
        "Munich": ["Mykonos"]
    }

    itinerary = []

    current_city = "Vilnius"
    current_day = 1

    # Day 1-4: Vilnius
    itinerary.append({"day_range": "Day 1-4", "place": "Vilnius"})

    # Fly to Munich on day 4
    if current_day == 4:
        next_city = "Munich"
        if next_city in flights.get(current_city, []):
            itinerary.append({"flying": "Day 4-4", "from": current_city, "to": next_city})
            current_day = 4
            current_city = next_city

    # Days 5-7: Munich
    if current_day >= 5 and current_city == "Munich":
        itinerary.append({"day_range": "Day 5-7", "place": "Munich"})

    # Fly to Mykonos on day 7
    if current_day == 7:
        next_city = "Mykonos"
        if next_city in flights.get(current_city, []):
            itinerary.append({"flying": "Day 7-7", "from": current_city, "to": next_city})
            current_day = 7
            current_city = next_city

    # Days 8-14: Mykonos
    if current_day >= 8 and current_city == "Mykonos":
        itinerary.append({"day_range": "Day 8-14", "place": "Mykonos"})

    return json.dumps(itinerary)

compute_itinerary()