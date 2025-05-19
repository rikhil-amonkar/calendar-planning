import json

def compute_itinerary():
    cities = {
        "Porto": {"days": 2},
        "Frankfurt": {"days": 2, "conference": [5, 6]},
        "Hamburg": {"days": 5},
        "Geneva": {"days": 3},
        "Mykonos": {"days": 3, "meeting": [10, 12]},
        "Manchester": {"days": 4, "wedding": [15, 18]},
        "Naples": {"days": 5}
    }

    flights = {
        "Porto": ["Hamburg", "Frankfurt"],
        "Frankfurt": ["Hamburg", "Naples"],
        "Hamburg": ["Geneva", "Mykonos"],
        "Geneva": ["Manchester"],
        "Mykonos": ["Naples"],
        "Naples": ["Manchester", "Geneva"],
        "Manchester": ["Naples"]
    }

    itinerary = []

    current_city = "Porto"
    current_day = 1

    # Day 1-2: Porto
    itinerary.append({"day_range": "Day 1-2", "place": "Porto"})

    # Fly to Frankfurt on day 2
    if current_day == 2:
        next_city = "Frankfurt"
        if next_city in flights.get(current_city, []):
            itinerary.append({"flying": "Day 2-2", "from": current_city, "to": next_city})
            current_day = 2
            current_city = next_city

    # Days 3-4: Frankfurt (conference)
    if current_day >= 3 and current_city == "Frankfurt":
        itinerary.append({"day_range": "Day 3-4", "place": "Frankfurt"})

    # Fly to Hamburg on day 4
    if current_day == 4:
        next_city = "Hamburg"
        if next_city in flights.get(current_city, []):
            itinerary.append({"flying": "Day 4-4", "from": current_city, "to": next_city})
            current_day = 4
            current_city = next_city

    # Days 5-8: Hamburg
    if current_day >= 5 and current_city == "Hamburg":
        itinerary.append({"day_range": "Day 5-8", "place": "Hamburg"})

    # Fly to Mykonos on day 8
    if current_day == 8:
        next_city = "Mykonos"
        if next_city in flights.get(current_city, []):
            itinerary.append({"flying": "Day 8-8", "from": current_city, "to": next_city})
            current_day = 8
            current_city = next_city

    # Days 9-11: Mykonos (meeting)
    if current_day >= 9 and current_city == "Mykonos":
        itinerary.append({"day_range": "Day 9-11", "place": "Mykonos"})

    # Fly to Naples on day 11
    if current_day == 11:
        next_city = "Naples"
        if next_city in flights.get(current_city, []):
            itinerary.append({"flying": "Day 11-11", "from": current_city, "to": next_city})
            current_day = 11
            current_city = next_city

    # Days 12-16: Naples
    if current_day >= 12 and current_city == "Naples":
        itinerary.append({"day_range": "Day 12-16", "place": "Naples"})

    # Fly to Manchester on day 16
    if current_day == 16:
        next_city = "Manchester"
        if next_city in flights.get(current_city, []):
            itinerary.append({"flying": "Day 16-16", "from": current_city, "to": next_city})
            current_day = 16
            current_city = next_city

    # Days 17-18: Manchester (wedding)
    if current_day >= 17 and current_city == "Manchester":
        itinerary.append({"day_range": "Day 17-18", "place": "Manchester"})

    return json.dumps(itinerary)

compute_itinerary()