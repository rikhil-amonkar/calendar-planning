import json

def compute_itinerary():
    cities = {
        "Tallinn": {"days": 2},
        "Bucharest": {"days": 4, "relatives": [1, 4]},
        "Seville": {"days": 5, "friends": [8, 12]},
        "Stockholm": {"days": 5},
        "Munich": {"days": 5, "wedding": [4, 8]},
        "Milan": {"days": 2}
    }

    flights = {
        "Tallinn": ["Stockholm"],
        "Stockholm": ["Munich"],
        "Munich": ["Bucharest", "Seville", "Milan"],
        "Bucharest": ["Munich"],
        "Seville": ["Milan"],
        "Milan": ["Tallinn"]
    }

    itinerary = []

    current_city = "Tallinn"
    current_day = 1

    # Day 1-2: Tallinn
    itinerary.append({"day_range": "Day 1-2", "place": "Tallinn"})

    # Fly to Stockholm on day 2
    if current_day == 2:
        next_city = "Stockholm"
        if next_city in flights.get(current_city, []):
            itinerary.append({"flying": "Day 2-2", "from": current_city, "to": next_city})
            current_day = 2
            current_city = next_city

    # Days 3-7: Stockholm
    if current_day >= 3 and current_city == "Stockholm":
        itinerary.append({"day_range": "Day 3-7", "place": "Stockholm"})

    # Fly to Munich on day 7
    if current_day == 7:
        next_city = "Munich"
        if next_city in flights.get(current_city, []):
            itinerary.append({"flying": "Day 7-7", "from": current_city, "to": next_city})
            current_day = 7
            current_city = next_city

    # Days 8-12: Munich (wedding)
    if current_day >= 8 and current_city == "Munich":
        itinerary.append({"day_range": "Day 8-12", "place": "Munich"})

    # Fly to Bucharest on day 12
    if current_day == 12:
        next_city = "Bucharest"
        if next_city in flights.get(current_city, []):
            itinerary.append({"flying": "Day 12-12", "from": current_city, "to": next_city})
            current_day = 12
            current_city = next_city

    # Days 13-16: Bucharest (relatives)
    if current_day >= 13 and current_city == "Bucharest":
        itinerary.append({"day_range": "Day 13-16", "place": "Bucharest"})

    # Fly to Seville on day 16
    if current_day == 16:
        next_city = "Seville"
        if next_city in flights.get(current_city, []):
            itinerary.append({"flying": "Day 16-16", "from": current_city, "to": next_city})
            current_day = 16
            current_city = next_city

    # Days 17-21: Seville (friends)
    if current_day >= 17 and current_city == "Seville":
        itinerary.append({"day_range": "Day 17-21", "place": "Seville"})

    # Fly to Milan on day 21
    if current_day == 21:
        next_city = "Milan"
        if next_city in flights.get(current_city, []):
            itinerary.append({"flying": "Day 21-21", "from": current_city, "to": next_city})
            current_day = 21
            current_city = next_city

    # Days 22-23: Milan
    if current_day >= 22 and current_city == "Milan":
        itinerary.append({"day_range": "Day 22-23", "place": "Milan"})

    return json.dumps(itinerary)

compute_itinerary()