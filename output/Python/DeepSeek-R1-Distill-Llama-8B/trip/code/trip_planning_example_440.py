# Read the input parameters and flight connections
cities = {
    "Split": 2,
    "Helsinki": 2,
    "Reykjavik": 3,
    "Vilnius": 3,
    "Geneva": 6
}

flights = {
    "Split": ["Helsinki", "Geneva"],
    "Helsinki": ["Reykjavik", "Vilnius", "Geneva"],
    "Reykjavik": ["Helsinki"],
    "Vilnius": ["Helsinki"],
    "Geneva": ["Split"]
}

# Itinerary construction
itinerary = []

# Starting city
current_city = "Split"
current_day = 1
itinerary.append({"day_range": f"Day {current_day}-{current_day + cities[current_city] - 1}", "place": current_city})

# Flight from Split to Helsinki on day 2
current_day += cities[current_city]
itinerary.append({"flying": f"Day {current_day - cities[current_city]}-{current_day}", "from": current_city, "to": "Helsinki"})

current_city = "Helsinki"
current_day = current_day - cities[current_city] + 1  # Day 2
itinerary.append({"day_range": f"Day {current_day}-{current_day + cities[current_city] - 1}", "place": current_city})

# Flight from Helsinki to Reykjavik on day 4
current_day += cities[current_city]
itinerary.append({"flying": f"Day {current_day - cities[current_city]}-{current_day}", "from": current_city, "to": "Reykjavik"})

current_city = "Reykjavik"
current_day = current_day - cities[current_city] + 1  # Day 4
itinerary.append({"day_range": f"Day {current_day}-{current_day + cities[current_city] - 1}", "place": current_city})

# Flight from Reykjavik to Vilnius on day 7
current_day += cities[current_city]
itinerary.append({"flying": f"Day {current_day - cities[current_city]}-{current_day}", "from": current_city, "to": "Vilnius"})

current_city = "Vilnius"
current_day = current_day - cities[current_city] + 1  # Day 7
itinerary.append({"day_range": f"Day {current_day}-{current_day + cities[current_city] - 1}", "place": current_city})

# Flight from Vilnius to Helsinki on day 10
current_day += cities[current_city]
itinerary.append({"flying": f"Day {current_day - cities[current_city]}-{current_day}", "from": current_city, "to": "Helsinki"})

current_city = "Helsinki"
current_day = current_day - cities[current_city] + 1  # Day 10
itinerary.append({"day_range": f"Day {current_day}-{current_day + cities[current_city] - 1}", "place": current_city})

# Flight from Helsinki to Geneva on day 12
current_day += cities[current_city]
itinerary.append({"flying": f"Day {current_day - cities[current_city]}-{current_day}", "from": current_city, "to": "Geneva"})

current_city = "Geneva"
current_day = current_day - cities[current_city] + 1  # Day 12
itinerary.append({"day_range": f"Day {current_day}-{current_day + cities[current_city] - 1}", "place": current_city})

# Output the itinerary as JSON
print(json.dumps(itinerary))