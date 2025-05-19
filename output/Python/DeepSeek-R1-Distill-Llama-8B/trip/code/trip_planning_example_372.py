import json

def compute_itinerary():
    cities = {
        "Seville": {"days": 2},
        "Stuttgart": {"days": 7, "conference": [7, 13]},
        "Porto": {"days": 3},
        "Madrid": {"days": 4, "relatives": [1, 4]}
    }

    flights = {
        "Seville": ["Porto"],
        "Porto": ["Stuttgart"],
        "Stuttgart": ["Madrid"],
        "Madrid": ["Seville"]
    }

    itinerary = []

    current_city = "Seville"
    current_day = 1

    # Day 1-2: Seville
    itinerary.append({"day_range": "Day 1-2", "place": "Seville"})

    # Fly to Porto on day 2
    if current_day == 2:
        next_city = "Porto"
        if next_city in flights.get(current_city, []):
            itinerary.append({"flying": "Day 2-2", "from": current_city, "to": next_city})
            current_day = 2
            current_city = next_city

    # Days 3-5: Porto
    if current_day >= 3 and current_city == "Porto":
        itinerary.append({"day_range": "Day 3-5", "place": "Porto"})

    # Fly to Stuttgart on day 5
    if current_day == 5:
        next_city = "Stuttgart"
        if next_city in flights.get(current_city, []):
            itinerary.append({"flying": "Day 5-5", "from": current_city, "to": next_city})
            current_day = 5
            current_city = next_city

    # Days 6-12: Stuttgart (conference)
    if current_day >= 6 and current_city == "Stuttgart":
        itinerary.append({"day_range": "Day 6-12", "place": "Stuttgart"})

    # Fly to Madrid on day 12
    if current_day == 12:
        next_city = "Madrid"
        if next_city in flights.get(current_city, []):
            itinerary.append({"flying": "Day 12-12", "from": current_city, "to": next_city})
            current_day = 12
            current_city = next_city

    # Days 13-16: Madrid
    if current_day >= 13 and current_city == "Madrid":
        itinerary.append({"day_range": "Day 13-16", "place": "Madrid"})

    return json.dumps(itinerary)

compute_itinerary()