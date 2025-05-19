# Read the input parameters and flight connections
cities = {
    "Reykjavik": 5,
    "Istanbul": 4,
    "Edinburgh": 5,
    "Oslo": 2,
    "Stuttgart": 3,
    "Bucharest": 5
}

flights = {
    "Reykjavik": ["Stuttgart"],
    "Stuttgart": ["Istanbul"],
    "Istanbul": ["Oslo", "Edinburgh"],
    "Oslo": ["Reykjavik", "Edinburgh", "Bucharest"],
    "Edinburgh": ["Istanbul", "Stuttgart"],
    "Bucharest": ["Istanbul"]
}

# Itinerary construction
itinerary = []

# Starting city
current_city = "Reykjavik"
current_day = 1
itinerary.append({"day_range": f"Day {current_day}-{current_day + cities[current_city] - 1}", "place": current_city})

# Flight from Reykjavik to Stuttgart on day 5
current_day += cities[current_city]
itinerary.append({"flying": f"Day {current_day - cities[current_city]}-{current_day}", "from": current_city, "to": "Stuttgart"})

current_city = "Stuttgart"
current_day = current_day - cities[current_city] + 1  # Day 5
itinerary.append({"day_range": f"Day {current_day}-{current_day + cities[current_city] - 1}", "place": current_city})

# Flight from Stuttgart to Istanbul on day 8
current_day += cities[current_city]
itinerary.append({"flying": f"Day {current_day - cities[current_city]}-{current_day}", "from": current_city, "to": "Istanbul"})

current_city = "Istanbul"
current_day = current_day - cities[current_city] + 1  # Day 8
itinerary.append({"day_range": f"Day {current_day}-{current_day + cities[current_city] - 1}", "place": current_city})

# Flight from Istanbul to Edinburgh on day 12
current_day += cities[current_city]
itinerary.append({"flying": f"Day {current_day - cities[current_city]}-{current_day}", "from": current_city, "to": "Edinburgh"})

current_city = "Edinburgh"
current_day = current_day - cities[current_city] + 1  # Day 12
itinerary.append({"day_range": f"Day {current_day}-{current_day + cities[current_city] - 1}", "place": current_city})

# Flight from Edinburgh to Oslo on day 17
current_day += cities[current_city]
itinerary.append({"flying": f"Day {current_day - cities[current_city]}-{current_day}", "from": current_city, "to": "Oslo"})

current_city = "Oslo"
current_day = current_day - cities[current_city] + 1  # Day 17
itinerary.append({"day_range": f"Day {current_day}-{current_day + cities[current_city] - 1}", "place": current_city})

# Flight from Oslo to Bucharest on day 19
current_day += cities[current_city]
itinerary.append({"flying": f"Day {current_day - cities[current_city]}-{current_day}", "from": current_city, "to": "Bucharest"})

current_city = "Bucharest"
current_day = current_day - cities[current_city] + 1  # Day 19
itinerary.append({"day_range": f"Day {current_day}-{current_day + cities[current_city] - 1}", "place": current_city})

# Output the itinerary as JSON
print(json.dumps(itinerary))