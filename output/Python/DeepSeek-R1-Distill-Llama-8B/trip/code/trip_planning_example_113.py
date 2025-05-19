# Read the input parameters and flight connections
cities = {
    "Naples": 3,
    "Seville": 4,
    "Milan": 7
}

flights = {
    "Milan": ["Seville"],
    "Seville": ["Naples"],
    "Naples": ["Milan"]
}

# Itinerary construction
itinerary = []

# Starting city
current_city = "Milan"
current_day = 1
itinerary.append({"day_range": f"Day {current_day}-{current_day + cities[current_city] - 1}", "place": current_city})

# Flight from Milan to Seville on day 7
current_day += cities[current_city]
itinerary.append({"flying": f"Day {current_day - cities[current_city]}-{current_day}", "from": current_city, "to": "Seville"})

current_city = "Seville"
current_day = current_day - cities[current_city] + 1  # Day 7
itinerary.append({"day_range": f"Day {current_day}-{current_day + cities[current_city] - 1}", "place": current_city})

# Flight from Seville to Naples on day 8
current_day += cities[current_city]
itinerary.append({"flying": f"Day {current_day - cities[current_city]}-{current_day}", "from": current_city, "to": "Naples"})

current_city = "Naples"
current_day = current_day - cities[current_city] + 1  # Day 8
itinerary.append({"day_range": f"Day {current_day}-{current_day + cities[current_city] - 1}", "place": current_city})

# Flight from Naples to Milan on day 10
current_day += cities[current_city]
itinerary.append({"flying": f"Day {current_day - cities[current_city]}-{current_day}", "from": current_city, "to": "Milan"})

current_city = "Milan"
current_day = current_day - cities[current_city] + 1  # Day 10
itinerary.append({"day_range": f"Day {current_day}-{current_day + cities[current_city] - 1}", "place": current_city})

# Output the itinerary as JSON
print(json.dumps(itinerary))