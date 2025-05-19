import json

def compute_itinerary():
    cities = {
        "Berlin": {"days": 3, "conference": [1, 3]},
        "Nice": {"days": 5},
        "Athens": {"days": 5},
        "Stockholm": {"days": 5},
        "Barcelona": {"days": 2, "workshop": [3, 4]},
        "Vilnius": {"days": 4},
        "Lyon": {"days": 2, "wedding": [4, 5]}
    }

    flights = {
        "Berlin": ["Barcelona", "Nice", "Athens", "Vilnius"],
        "Nice": ["Barcelona", "Athens", "Stockholm"],
        "Athens": ["Berlin", "Vilnius"],
        "Barcelona": ["Nice", "Athens", "Stockholm", "Lyon"],
        "Vilnius": ["Berlin", "Athens"],
        "Lyon": ["Nice"]
    }

    itinerary = []

    current_city = "Berlin"
    current_day = 1

    # Day 1-3: Berlin (conference)
    itinerary.append({"day_range": "Day 1-3", "place": "Berlin"})

    # Fly to Barcelona on day 3
    if current_day == 3:
        next_city = "Barcelona"
        if next_city in flights.get(current_city, []):
            itinerary.append({"flying": "Day 3-3", "from": current_city, "to": next_city})
            current_day = 3
            current_city = next_city

    # Days 4-5: Barcelona (workshop)
    if current_day >= 4 and current_city == "Barcelona":
        itinerary.append({"day_range": "Day 4-5", "place": "Barcelona"})

    # Fly to Nice on day 5
    if current_day == 5:
        next_city = "Nice"
        if next_city in flights.get(current_city, []):
            itinerary.append({"flying": "Day 5-5", "from": current_city, "to": next_city})
            current_day = 5
            current_city = next_city

    # Days 6-9: Nice
    if current_day >= 6 and current_city == "Nice":
        itinerary.append({"day_range": "Day 6-9", "place": "Nice"})

    # Fly to Stockholm on day 9
    if current_day == 9:
        next_city = "Stockholm"
        if next_city in flights.get(current_city, []):
            itinerary.append({"flying": "Day 9-9", "from": current_city, "to": next_city})
            current_day = 9
            current_city = next_city

    # Days 10-14: Stockholm
    if current_day >= 10 and current_city == "Stockholm":
        itinerary.append({"day_range": "Day 10-14", "place": "Stockholm"})

    # Fly to Athens on day 14
    if current_day == 14:
        next_city = "Athens"
        if next_city in flights.get(current_city, []):
            itinerary.append({"flying": "Day 14-14", "from": current_city, "to": next_city})
            current_day = 14
            current_city = next_city

    # Days 15-19: Athens
    if current_day >= 15 and current_city == "Athens":
        itinerary.append({"day_range": "Day 15-19", "place": "Athens"})

    # Fly to Vilnius on day 19
    if current_day == 19:
        next_city = "Vilnius"
        if next_city in flights.get(current_city, []):
            itinerary.append({"flying": "Day 19-19", "from": current_city, "to": next_city})
            current_day = 19
            current_city = next_city

    # Days 20: Vilnius
    if current_day >= 20 and current_city == "Vilnius":
        itinerary.append({"day_range": "Day 20-20", "place": "Vilnius"})

    return json.dumps(itinerary)

compute_itinerary()