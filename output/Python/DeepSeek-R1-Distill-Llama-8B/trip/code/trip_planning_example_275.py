# Read the input parameters and flight connections
cities = {
    "Split": 5,
    "Vilnius": 4,
    "Santorini": 2,
    "Madrid": 6
}

flights = {
    "Vilnius": ["Split"],
    "Split": ["Madrid"],
    "Madrid": ["Santorini"]
}

# Itinerary construction
itinerary = []

# Starting city
current_city = "Madrid"
current_day = 1
itinerary.append({"day_range": f"Day {current_day}-{current_day + cities[current_city] - 1}", "place": current_city})

# Flight from Madrid to Vilnius on day 6
current_day += cities[current_city]
itinerary.append({"flying": f"Day {current_day - cities[current_city]}-{current_day}", "from": current_city, "to": "Vilnius"})

current_city = "Vilnius"
current_day = current_day - cities[current_city] + 1  # Day 6
itinerary.append({"day_range": f"Day {current_day}-{current_day + cities[current_city] - 1}", "place": current_city})

# Flight from Vilnius to Split on day 10
current_day += cities[current_city]
itinerary.append({"flying": f"Day {current_day - cities[current_city]}-{current_day}", "from": current_city, "to": "Split"})

current_city = "Split"
current_day = current_day - cities[current_city] + 1  # Day 10
itinerary.append({"day_range": f"Day {current_day}-{current_day + cities[current_city] - 1}", "place": current_city})

# Flight from Split to Madrid on day 14
current_day += cities[current_city]
itinerary.append({"flying": f"Day {current_day - cities[current_city]}-{current_day}", "from": current_city, "to": "Madrid"})

current_city = "Madrid"
current_day = current_day - cities[current_city] + 1  # Day 14
itinerary.append({"day_range": f"Day {current_day}-{current_day + cities[current_city] - 1}", "place": current_city})

# Flight from Madrid to Santorini on day 14
current_day += cities[current_city]
itinerary.append({"flying": f"Day {current_day - cities[current_city]}-{current_day}", "from": current_city, "to": "Santorini"})

current_city = "Santorini"
current_day = current_day - cities[current_city] + 1  # Day 14
itinerary.append({"day_range": f"Day {current_day}-{current_day + cities[current_city] - 1}", "place": current_city})

# Output the itinerary as JSON
print(json.dumps(itinerary))