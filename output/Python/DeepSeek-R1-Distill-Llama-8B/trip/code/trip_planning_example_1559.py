import json

def compute_itinerary():
    cities = {
        "Valencia": {"days": 2, "friends": [3, 4]},
        "Oslo": {"days": 3, "friend": [13, 15]},
        "Lyon": {"days": 4},
        "Prague": {"days": 3},
        "Paris": {"days": 4},
        "Nice": {"days": 4},
        "Seville": {"days": 5, "show": [5, 9]},
        "Tallinn": {"days": 2},
        "Mykonos": {"days": 5, "wedding": [21, 25]},
        "Lisbon": {"days": 2}
    }

    flights = {
        "Valencia": ["Paris"],
        "Paris": ["Seville", "Nice", "Tallinn", "Lisbon"],
        "Seville": ["Nice"],
        "Nice": ["Mykonos"],
        "Mykonos": ["Lisbon"],
        "Tallinn": ["Paris"],
        "Lisbon": ["Paris"],
        "Oslo": ["Nice"]
    }

    itinerary = []

    current_city = "Valencia"
    current_day = 1

    # Day 1-2: Valencia (friends)
    itinerary.append({"day_range": "Day 1-2", "place": "Valencia"})

    # Fly to Paris on day 2
    if current_day == 2:
        next_city = "Paris"
        if next_city in flights.get(current_city, []):
            itinerary.append({"flying": "Day 2-2", "from": current_city, "to": next_city})
            current_day = 2
            current_city = next_city

    # Days 3-7: Paris
    if current_day >= 3 and current_city == "Paris":
        itinerary.append({"day_range": "Day 3-7", "place": "Paris"})

    # Fly to Seville on day 7
    if current_day == 7:
        next_city = "Seville"
        if next_city in flights.get(current_city, []):
            itinerary.append({"flying": "Day 7-7", "from": current_city, "to": next_city})
            current_day = 7
            current_city = next_city

    # Days 8-14: Seville (show)
    if current_day >= 8 and current_city == "Seville":
        itinerary.append({"day_range": "Day 8-14", "place": "Seville"})

    # Fly to Nice on day 14
    if current_day == 14:
        next_city = "Nice"
        if next_city in flights.get(current_city, []):
            itinerary.append({"flying": "Day 14-14", "from": current_city, "to": next_city})
            current_day = 14
            current_city = next_city

    # Days 15-19: Nice
    if current_day >= 15 and current_city == "Nice":
        itinerary.append({"day_range": "Day 15-19", "place": "Nice"})

    # Fly to Mykonos on day 19
    if current_day == 19:
        next_city = "Mykonos"
        if next_city in flights.get(current_city, []):
            itinerary.append({"flying": "Day 19-19", "from": current_city, "to": next_city})
            current_day = 19
            current_city = next_city

    # Days 20-24: Mykonos (wedding)
    if current_day >= 20 and current_city == "Mykonos":
        itinerary.append({"day_range": "Day 20-24", "place": "Mykonos"})

    # Fly to Tallinn on day 24
    if current_day == 24:
        next_city = "Tallinn"
        if next_city in flights.get(current_city, []):
            itinerary.append({"flying": "Day 24-24", "from": current_city, "to": next_city})
            current_day = 24
            current_city = next_city

    # Days 25: Tallinn
    if current_day >= 25 and current_city == "Tallinn":
        itinerary.append({"day_range": "Day 25-25", "place": "Tallinn"})

    # Convert to JSON
    return json.dumps(itinerary)

compute_itinerary()