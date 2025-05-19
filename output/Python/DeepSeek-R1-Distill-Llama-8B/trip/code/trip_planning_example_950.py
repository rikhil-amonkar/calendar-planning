# Read the input parameters and flight connections
cities = {
    "Mykonos": 3,
    "Riga": 3,
    "Munich": 4,
    "Bucharest": 4,
    "Rome": 4,
    "Nice": 3,
    "Krakow": 2
}

flights = {
    "Mykonos": ["Munich", "Nice"],
    "Riga": ["Bucharest"],
    "Munich": ["Mykonos", "Krakow"],
    "Bucharest": ["Riga"],
    "Rome": ["Nice", "Munich", "Mykonos"],
    "Nice": ["Rome", "Munich"],
    "Krakow": ["Munich"]
}

# Itinerary construction
itinerary = []

# Starting city
current_city = "Mykonos"
current_day = 1
itinerary.append({"day_range": f"Day {current_day}-{current_day + cities[current_city] - 1}", "place": current_city})

# Flight from Mykonos to Munich on day 3
current_day += cities[current_city]
itinerary.append({"flying": f"Day {current_day - cities[current_city]}-{current_day}", "from": current_city, "to": "Munich"})

current_city = "Munich"
current_day = current_day - cities[current_city] + 1  # Day 3
itinerary.append({"day_range": f"Day {current_day}-{current_day + cities[current_city] - 1}", "place": current_city})

# Flight from Munich to Krakow on day 6
current_day += cities[current_city]
itinerary.append({"flying": f"Day {current_day - cities[current_city]}-{current_day}", "from": current_city, "to": "Krakow"})

current_city = "Krakow"
current_day = current_day - cities[current_city] + 1  # Day 6
itinerary.append({"day_range": f"Day {current_day}-{current_day + cities[current_city] - 1}", "place": current_city})

# Flight from Krakow to Munich on day 8
current_day += cities[current_city]
itinerary.append({"flying": f"Day {current_day - cities[current_city]}-{current_day}", "from": current_city, "to": "Munich"})

current_city = "Munich"
current_day = current_day - cities[current_city] + 1  # Day 8
itinerary.append({"day_range": f"Day {current_day}-{current_day + cities[current_city] - 1}", "place": current_city})

# Flight from Munich to Rome on day 12
current_day += cities[current_city]
itinerary.append({"flying": f"Day {current_day - cities[current_city]}-{current_day}", "from": current_city, "to": "Rome"})

current_city = "Rome"
current_day = current_day - cities[current_city] + 1  # Day 12
itinerary.append({"day_range": f"Day {current_day}-{current_day + cities[current_city] - 1}", "place": current_city})

# Flight from Rome to Nice on day 16
current_day += cities[current_city]
itinerary.append({"flying": f"Day {current_day - cities[current_city]}-{current_day}", "from": current_city, "to": "Nice"})

current_city = "Nice"
current_day = current_day - cities[current_city] + 1  # Day 16
itinerary.append({"day_range": f"Day {current_day}-{current_day + cities[current_city] - 1}", "place": current_city})

# Flight from Nice to Bucharest on day 19
current_day += cities[current_city]
itinerary.append({"flying": f"Day {current_day - cities[current_city]}-{current_day}", "from": current_city, "to": "Bucharest"})

current_city = "Bucharest"
current_day = current_day - cities[current_city] + 1  # Day 19
itinerary.append({"day_range": f"Day {current_day}-{current_day + cities[current_city] - 1}", "place": current_city})

# Output the itinerary as JSON
print(json.dumps(itinerary))