import json

def compute_itinerary():
    cities = {
        "Paris": {"days": 2, "workshop": [1, 2]},
        "Warsaw": {"days": 4},
        "Venice": {"days": 3},
        "Vilnius": {"days": 3},
        "Salzburg": {"days": 4, "wedding": [22, 25]},
        "Amsterdam": {"days": 2},
        "Barcelona": {"days": 5, "tour": [2, 6]},
        "Hamburg": {"days": 4, "conference": [19, 22]},
        "Florence": {"days": 5},
        "Tallinn": {"days": 2, "friend": [11, 12]}
    }

    flights = {
        "Paris": ["Warsaw", "Amsterdam", "Vilnius", "Barcelona"],
        "Warsaw": ["Paris", "Venice", "Vilnius"],
        "Venice": ["Warsaw", "Hamburg"],
        "Vilnius": ["Warsaw", "Paris"],
        "Barcelona": ["Warsaw", "Amsterdam", "Hamburg", "Florence"],
        "Amsterdam": ["Paris", "Warsaw", "Vilnius", "Tallinn"],
        "Hamburg": ["Florence", "Salzburg"],
        "Florence": ["Hamburg", "Barcelona"],
        "Tallinn": ["Warsaw", "Vilnius"],
        "Salzburg": ["Hamburg"]
    }

    itinerary = []

    current_city = "Paris"
    current_day = 1

    # Day 1-2: Paris (workshop)
    itinerary.append({"day_range": "Day 1-2", "place": "Paris"})

    # Fly to Barcelona on day 2
    if current_day == 2:
        next_city = "Barcelona"
        if next_city in flights.get(current_city, []):
            itinerary.append({"flying": "Day 2-2", "from": current_city, "to": next_city})
            current_day = 2
            current_city = next_city

    # Days 3-7: Barcelona (tour)
    if current_day >= 3 and current_city == "Barcelona":
        itinerary.append({"day_range": "Day 3-7", "place": "Barcelona"})

    # Fly to Warsaw on day 7
    if current_day == 7:
        next_city = "Warsaw"
        if next_city in flights.get(current_city, []):
            itinerary.append({"flying": "Day 7-7", "from": current_city, "to": next_city})
            current_day = 7
            current_city = next_city

    # Days 8-11: Warsaw
    if current_day >= 8 and current_city == "Warsaw":
        itinerary.append({"day_range": "Day 8-11", "place": "Warsaw"})

    # Fly to Venice on day 11
    if current_day == 11:
        next_city = "Venice"
        if next_city in flights.get(current_city, []):
            itinerary.append({"flying": "Day 11-11", "from": current_city, "to": next_city})
            current_day = 11
            current_city = next_city

    # Days 12-14: Venice
    if current_day >= 12 and current_city == "Venice":
        itinerary.append({"day_range": "Day 12-14", "place": "Venice"})

    # Fly to Vilnius on day 14
    if current_day == 14:
        next_city = "Vilnius"
        if next_city in flights.get(current_city, []):
            itinerary.append({"flying": "Day 14-14", "from": current_city, "to": next_city})
            current_day = 14
            current_city = next_city

    # Days 15-17: Vilnius
    if current_day >= 15 and current_city == "Vilnius":
        itinerary.append({"day_range": "Day 15-17", "place": "Vilnius"})

    # Fly to Hamburg on day 17
    if current_day == 17:
        next_city = "Hamburg"
        if next_city in flights.get(current_city, []):
            itinerary.append({"flying": "Day 17-17", "from": current_city, "to": next_city})
            current_day = 17
            current_city = next_city

    # Days 18-21: Hamburg (conference)
    if current_day >= 18 and current_city == "Hamburg":
        itinerary.append({"day_range": "Day 18-21", "place": "Hamburg"})

    # Fly to Salzburg on day 21
    if current_day == 21:
        next_city = "Salzburg"
        if next_city in flights.get(current_city, []):
            itinerary.append({"flying": "Day 21-21", "from": current_city, "to": next_city})
            current_day = 21
            current_city = next_city

    # Days 22-25: Salzburg (wedding)
    if current_day >= 22 and current_city == "Salzburg":
        itinerary.append({"day_range": "Day 22-25", "place": "Salzburg"})

    return json.dumps(itinerary)

compute_itinerary()