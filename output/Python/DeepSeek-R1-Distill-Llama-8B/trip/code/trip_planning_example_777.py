# Read the input parameters and flight connections
cities = {
    "Dublin": 5,
    "Helsinki": 3,
    "Riga": 3,
    "Reykjavik": 2,
    "Vienna": 2,
    "Tallinn": 5
}

flights = {
    "Dublin": ["Helsinki", "Riga"],
    "Helsinki": ["Riga"],
    "Riga": ["Vienna"],
    "Vienna": ["Riga"],
    "Reykjavik": ["Helsinki"],
    "Tallinn": ["Dublin"]
}

# Itinerary construction
itinerary = []

# Starting city
current_city = "Dublin"
current_day = 1
itinerary.append({"day_range": f"Day {current_day}-{current_day + cities[current_city] - 1}", "place": current_city})

# Flight from Dublin to Helsinki on day 5
current_day += cities[current_city]
itinerary.append({"flying": f"Day {current_day - cities[current_city]}-{current_day}", "from": current_city, "to": "Helsinki"})

current_city = "Helsinki"
current_day = current_day - cities[current_city] + 1  # Day 5
itinerary.append({"day_range": f"Day {current_day}-{current_day + cities[current_city] - 1}", "place": current_city})

# Flight from Helsinki to Riga on day 7
current_day += cities[current_city]
itinerary.append({"flying": f"Day {current_day - cities[current_city]}-{current_day}", "from": current_city, "to": "Riga"})

current_city = "Riga"
current_day = current_day - cities[current_city] + 1  # Day 7
itinerary.append({"day_range": f"Day {current_day}-{current_day + cities[current_city] - 1}", "place": current_city})

# Flight from Riga to Vienna on day 9
current_day += cities[current_city]
itinerary.append({"flying": f"Day {current_day - cities[current_city]}-{current_day}", "from": current_city, "to": "Vienna"})

current_city = "Vienna"
current_day = current_day - cities[current_city] + 1  # Day 9
itinerary.append({"day_range": f"Day {current_day}-{current_day + cities[current_city] - 1}", "place": current_city})

# Flight from Vienna to Riga on day 10
current_day += cities[current_city]
itinerary.append({"flying": f"Day {current_day - cities[current_city]}-{current_day}", "from": current_city, "to": "Riga"})

current_city = "Riga"
current_day = current_day - cities[current_city] + 1  # Day 10
itinerary.append({"day_range": f"Day {current_day}-{current_day + cities[current_city] - 1}", "place": current_city})

# Flight from Riga to Tallinn on day 12
current_day += cities[current_city]
itinerary.append({"flying": f"Day {current_day - cities[current_city]}-{current_day}", "from": current_city, "to": "Tallinn"})

current_city = "Tallinn"
current_day = current_day - cities[current_city] + 1  # Day 12
itinerary.append({"day_range": f"Day {current_day}-{current_day + cities[current_city] - 1}", "place": current_city})

# Flight from Tallinn to Dublin on day 16
current_day += cities[current_city]
itinerary.append({"flying": f"Day {current_day - cities[current_city]}-{current_day}", "from": current_city, "to": "Dublin"})

current_city = "Dublin"
current_day = current_day - cities[current_city] + 1  # Day 16
itinerary.append({"day_range": f"Day {current_day}-{current_day + cities[current_city] - 1}", "place": current_city})

# Output the itinerary as JSON
print(json.dumps(itinerary))