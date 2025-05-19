# Read the input parameters and flight connections
cities = {
    "Helsinki": 4,
    "Valencia": 5,
    "Dubrovnik": 4,
    "Porto": 3,
    "Prague": 3,
    "Reykjavik": 3
}

flights = {
    "Helsinki": ["Reykjavik", "Dubrovnik"],
    "Reykjavik": ["Prague"],
    "Prague": ["Valencia"],
    "Valencia": ["Porto"],
    "Dubrovnik": ["Helsinki"],
    "Porto": []
}

# Itinerary construction
itinerary = []

# Starting city
current_city = "Helsinki"
current_day = 1
itinerary.append({"day_range": f"Day {current_day}-{current_day + cities[current_city] - 1}", "place": current_city})

# Flight from Helsinki to Reykjavik on day 4
current_day += cities[current_city]
itinerary.append({"flying": f"Day {current_day - cities[current_city]}-{current_day}", "from": current_city, "to": "Reykjavik"})

current_city = "Reykjavik"
current_day = current_day - cities[current_city] + 1  # Day 4
itinerary.append({"day_range": f"Day {current_day}-{current_day + cities[current_city] - 1}", "place": current_city})

# Flight from Reykjavik to Prague on day 7
current_day += cities[current_city]
itinerary.append({"flying": f"Day {current_day - cities[current_city]}-{current_day}", "from": current_city, "to": "Prague"})

current_city = "Prague"
current_day = current_day - cities[current_city] + 1  # Day 7
itinerary.append({"day_range": f"Day {current_day}-{current_day + cities[current_city] - 1}", "place": current_city})

# Flight from Prague to Valencia on day 10
current_day += cities[current_city]
itinerary.append({"flying": f"Day {current_day - cities[current_city]}-{current_day}", "from": current_city, "to": "Valencia"})

current_city = "Valencia"
current_day = current_day - cities[current_city] + 1  # Day 10
itinerary.append({"day_range": f"Day {current_day}-{current_day + cities[current_city] - 1}", "place": current_city})

# Flight from Valencia to Dubrovnik on day 14
current_day += cities[current_city]
itinerary.append({"flying": f"Day {current_day - cities[current_city]}-{current_day}", "from": current_city, "to": "Dubrovnik"})

current_city = "Dubrovnik"
current_day = current_day - cities[current_city] + 1  # Day 14
itinerary.append({"day_range": f"Day {current_day}-{current_day + cities[current_city] - 1}", "place": current_city})

# Flight from Dubrovnik to Helsinki on day 17
current_day += cities[current_city]
itinerary.append({"flying": f"Day {current_day - cities[current_city]}-{current_day}", "from": current_city, "to": "Helsinki"})

current_city = "Helsinki"
current_day = current_day - cities[current_city] + 1  # Day 17
itinerary.append({"day_range": f"Day {current_day}-{current_day + cities[current_city] - 1}", "place": current_city})

# Output the itinerary as JSON
print(json.dumps(itinerary))