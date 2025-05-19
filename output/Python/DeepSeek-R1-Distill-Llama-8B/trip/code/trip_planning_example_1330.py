# Read the input parameters and flight connections
cities = {
    "Salzburg": 2,
    "Venice": 5,
    "Bucharest": 4,
    "Brussels": 2,
    "Hamburg": 4,
    "Copenhagen": 4,
    "Nice": 3,
    "Zurich": 5,
    "Naples": 4
}

flights = {
    "Salzburg": ["Zurich"],
    "Venice": ["Brussels"],
    "Bucharest": ["Copenhagen"],
    "Brussels": ["Zurich", "Nice"],
    "Hamburg": ["Nice", "Zurich"],
    "Copenhagen": ["Brussels", "Naples"],
    "Nice": ["Zurich", "Naples"],
    "Zurich": ["Brussels", "Naples"],
    "Naples": ["Hamburg"]
}

# Itinerary construction
itinerary = []

# Starting city
current_city = "Salzburg"
current_day = 1
itinerary.append({"day_range": f"Day {current_day}-{current_day + cities[current_city] - 1}", "place": current_city})

# Flight from Salzburg to Zurich on day 2
current_day += cities[current_city]
itinerary.append({"flying": f"Day {current_day - cities[current_city]}-{current_day}", "from": current_city, "to": "Zurich"})

current_city = "Zurich"
current_day = current_day - cities[current_city] + 1  # Day 2
itinerary.append({"day_range": f"Day {current_day}-{current_day + cities[current_city] - 1}", "place": current_city})

# Flight from Zurich to Brussels on day 3
current_day += cities[current_city]
itinerary.append({"flying": f"Day {current_day - cities[current_city]}-{current_day}", "from": current_city, "to": "Brussels"})

current_city = "Brussels"
current_day = current_day - cities[current_city] + 1  # Day 3
itinerary.append({"day_range": f"Day {current_day}-{current_day + cities[current_city] - 1}", "place": current_city})

# Flight from Brussels to Nice on day 5
current_day += cities[current_city]
itinerary.append({"flying": f"Day {current_day - cities[current_city]}-{current_day}", "from": current_city, "to": "Nice"})

current_city = "Nice"
current_day = current_day - cities[current_city] + 1  # Day 5
itinerary.append({"day_range": f"Day {current_day}-{current_day + cities[current_city] - 1}", "place": current_city})

# Flight from Nice to Zurich on day 7
current_day += cities[current_city]
itinerary.append({"flying": f"Day {current_day - cities[current_city]}-{current_day}", "from": current_city, "to": "Zurich"})

current_city = "Zurich"
current_day = current_day - cities[current_city] + 1  # Day 7
itinerary.append({"day_range": f"Day {current_day}-{current_day + cities[current_city] - 1}", "place": current_city})

# Flight from Zurich to Naples on day 10
current_day += cities[current_city]
itinerary.append({"flying": f"Day {current_day - cities[current_city]}-{current_day}", "from": current_city, "to": "Naples"})

current_city = "Naples"
current_day = current_day - cities[current_city] + 1  # Day 10
itinerary.append({"day_range": f"Day {current_day}-{current_day + cities[current_city] - 1}", "place": current_city})

# Flight from Naples to Hamburg on day 13
current_day += cities[current_city]
itinerary.append({"flying": f"Day {current_day - cities[current_city]}-{current_day}", "from": current_city, "to": "Hamburg"})

current_city = "Hamburg"
current_day = current_day - cities[current_city] + 1  # Day 13
itinerary.append({"day_range": f"Day {current_day}-{current_day + cities[current_city] - 1}", "place": current_city})

# Flight from Hamburg to Bucharest on day 16
current_day += cities[current_city]
itinerary.append({"flying": f"Day {current_day - cities[current_city]}-{current_day}", "from": current_city, "to": "Bucharest"})

current_city = "Bucharest"
current_day = current_day - cities[current_city] + 1  # Day 16
itinerary.append({"day_range": f"Day {current_day}-{current_day + cities[current_city] - 1}", "place": current_city})

# Flight from Bucharest to Copenhagen on day 19
current_day += cities[current_city]
itinerary.append({"flying": f"Day {current_day - cities[current_city]}-{current_day}", "from": current_city, "to": "Copenhagen"})

current_city = "Copenhagen"
current_day = current_day - cities[current_city] + 1  # Day 19
itinerary.append({"day_range": f"Day {current_day}-{current_day + cities[current_city] - 1}", "place": current_city})

# Flight from Copenhagen to Brussels on day 22
current_day += cities[current_city]
itinerary.append({"flying": f"Day {current_day - cities[current_city]}-{current_day}", "from": current_city, "to": "Brussels"})

current_city = "Brussels"
current_day = current_day - cities[current_city] + 1  # Day 22
itinerary.append({"day_range": f"Day {current_day}-{current_day + cities[current_city] - 1}", "place": current_city})

# Flight from Brussels to Nice on day 24
current_day += cities[current_city]
itinerary.append({"flying": f"Day {current_day - cities[current_city]}-{current_day}", "from": current_city, "to": "Nice"})

current_city = "Nice"
current_day = current_day - cities[current_city] + 1  # Day 24
itinerary.append({"day_range": f"Day {current_day}-{current_day + cities[current_city] - 1}", "place": current_city})

# Flight from Nice to Naples on day 25
current_day += cities[current_city]
itinerary.append({"flying": f"Day {current_day - cities[current_city]}-{current_day}", "from": current_city, "to": "Naples"})

current_city = "Naples"
current_day = current_day - cities[current_city] + 1  # Day 25
itinerary.append({"day_range": f"Day {current_day}-{current_day + cities[current_city] - 1}", "place": current_city})

# Output the itinerary as JSON
print(json.dumps(itinerary))