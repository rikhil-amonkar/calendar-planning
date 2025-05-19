import json

def compute_itinerary():
    cities = {
        "Paris": {"days": 6},
        "Madrid": {"days": 7, "show": [1, 7]},
        "Bucharest": {"days": 2, "relatives": [14, 15]},
        "Seville": {"days": 3}
    }

    flights = {
        "Paris": ["Madrid"],
        "Madrid": ["Seville"],
        "Seville": ["Bucharest"]
    }

    itinerary = []

    current_city = "Paris"
    current_day = 1

    # Day 1-6: Paris
    itinerary.append({"day_range": "Day 1-6", "place": "Paris"})

    # Fly to Madrid on day 6
    if current_day == 6:
        next_city = "Madrid"
        if next_city in flights.get(current_city, []):
            itinerary.append({"flying": "Day 6-6", "from": current_city, "to": next_city})
            current_day = 6
            current_city = next_city

    # Days 7-13: Madrid (show)
    if current_day >= 7 and current_city == "Madrid":
        itinerary.append({"day_range": "Day 7-13", "place": "Madrid"})

    # Fly to Seville on day 13
    if current_day == 13:
        next_city = "Seville"
        if next_city in flights.get(current_city, []):
            itinerary.append({"flying": "Day 13-13", "from": current_city, "to": next_city})
            current_day = 13
            current_city = next_city

    # Days 14-16: Seville
    if current_day >= 14 and current_city == "Seville":
        itinerary.append({"day_range": "Day 14-16", "place": "Seville"})

    # Fly to Bucharest on day 16
    if current_day == 16:
        next_city = "Bucharest"
        if next_city in flights.get(current_city, []):
            itinerary.append({"flying": "Day 16-16", "from": current_city, "to": next_city})
            current_day = 16
            current_city = next_city

    # Days 17-18: Bucharest (relatives)
    if current_day >= 17 and current_city == "Bucharest":
        itinerary.append({"day_range": "Day 17-18", "place": "Bucharest"})

    return json.dumps(itinerary)

compute_itinerary()