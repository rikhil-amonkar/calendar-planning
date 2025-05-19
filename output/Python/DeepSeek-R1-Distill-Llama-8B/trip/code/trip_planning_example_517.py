import json

def compute_itinerary():
    cities = {
        "Dubrovnik": {"days": 5},
        "Warsaw": {"days": 2},
        "Stuttgart": {"days": 7, "conference": [7, 13]},
        "Bucharest": {"days": 6, "wedding": [1, 6]},
        "Copenhagen": {"days": 3}
    }

    flights = {
        "Dubrovnik": ["Warsaw"],
        "Warsaw": ["Dubrovnik", "Stuttgart", "Copenhagen"],
        "Stuttgart": ["Copenhagen"],
        "Bucharest": ["Copenhagen"],
        "Copenhagen": ["Bucharest"]
    }

    itinerary = []

    current_city = "Dubrovnik"
    current_day = 1

    # Day 1-5: Dubrovnik
    itinerary.append({"day_range": "Day 1-5", "place": "Dubrovnik"})

    # Fly to Warsaw on day 5
    if current_day == 5:
        next_city = "Warsaw"
        if next_city in flights.get(current_city, []):
            itinerary.append({"flying": "Day 5-5", "from": current_city, "to": next_city})
            current_day = 5
            current_city = next_city

    # Days 6-7: Warsaw
    if current_day >= 6 and current_city == "Warsaw":
        itinerary.append({"day_range": "Day 6-7", "place": "Warsaw"})

    # Fly to Stuttgart on day 7
    if current_day == 7:
        next_city = "Stuttgart"
        if next_city in flights.get(current_city, []):
            itinerary.append({"flying": "Day 7-7", "from": current_city, "to": next_city})
            current_day = 7
            current_city = next_city

    # Days 8-14: Stuttgart (conference)
    if current_day >= 8 and current_city == "Stuttgart":
        itinerary.append({"day_range": "Day 8-14", "place": "Stuttgart"})

    # Fly to Bucharest on day 14
    if current_day == 14:
        next_city = "Bucharest"
        if next_city in flights.get(current_city, []):
            itinerary.append({"flying": "Day 14-14", "from": current_city, "to": next_city})
            current_day = 14
            current_city = next_city

    # Days 15-20: Bucharest (wedding)
    if current_day >= 15 and current_city == "Bucharest":
        itinerary.append({"day_range": "Day 15-20", "place": "Bucharest"})

    # Fly to Copenhagen on day 20
    if current_day == 20:
        next_city = "Copenhagen"
        if next_city in flights.get(current_city, []):
            itinerary.append({"flying": "Day 20-20", "from": current_city, "to": next_city})
            current_day = 20
            current_city = next_city

    # Days 21-23: Copenhagen
    if current_day >= 21 and current_city == "Copenhagen":
        itinerary.append({"day_range": "Day 21-23", "place": "Copenhagen"})

    return json.dumps(itinerary)

compute_itinerary()