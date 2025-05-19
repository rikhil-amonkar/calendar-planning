# Read the input parameters and flight connections
cities = {
    "Prague": 5,
    "Tallinn": 3,
    "Warsaw": 2,
    "Porto": 3,
    "Naples": 5,
    "Milan": 3,
    "Lisbon": 5,
    "Santorini": 5,
    "Riga": 4,
    "Stockholm": 2
}

flights = {
    "Riga": ["Tallinn", "Stockholm", "Warsaw"],
    "Tallinn": ["Prague"],
    "Warsaw": ["Porto"],
    "Porto": ["Lisbon"],
    "Lisbon": ["Naples", "Milan"],
    "Naples": ["Warsaw"],
    "Milan": ["Lisbon", "Santorini"],
    "Santorini": ["Milan"],
    "Riga": ["Prague"],
    "Stockholm": ["Prague", "Tallinn"],
    "Prague": ["Riga", "Tallinn", "Warsaw"]
}

# Itinerary construction
itinerary = []

# Starting city
current_city = "Riga"
current_day = 1
itinerary.append({"day_range": f"Day {current_day}-{current_day + cities[current_city] - 1}", "place": current_city})

# Flight from Riga to Tallinn on day 2
current_day += cities[current_city]
itinerary.append({"flying": f"Day {current_day - cities[current_city]}-{current_day}", "from": current_city, "to": "Tallinn"})

current_city = "Tallinn"
current_day = current_day - cities[current_city] + 1  # Day 2
itinerary.append({"day_range": f"Day {current_day}-{current_day + cities[current_city] - 1}", "place": current_city})

# Flight from Tallinn to Prague on day 5
current_day += cities[current_city]
itinerary.append({"flying": f"Day {current_day - cities[current_city]}-{current_day}", "from": current_city, "to": "Prague"})

current_city = "Prague"
current_day = current_day - cities[current_city] + 1  # Day 5
itinerary.append({"day_range": f"Day {current_day}-{current_day + cities[current_city] - 1}", "place": current_city})

# Flight from Prague to Warsaw on day 8
current_day += cities[current_city]
itinerary.append({"flying": f"Day {current_day - cities[current_city]}-{current_day}", "from": current_city, "to": "Warsaw"})

current_city = "Warsaw"
current_day = current_day - cities[current_city] + 1  # Day 8
itinerary.append({"day_range": f"Day {current_day}-{current_day + cities[current_city] - 1}", "place": current_city})

# Flight from Warsaw to Porto on day 10
current_day += cities[current_city]
itinerary.append({"flying": f"Day {current_day - cities[current_city]}-{current_day}", "from": current_city, "to": "Porto"})

current_city = "Porto"
current_day = current_day - cities[current_city] + 1  # Day 10
itinerary.append({"day_range": f"Day {current_day}-{current_day + cities[current_city] - 1}", "place": current_city})

# Flight from Porto to Lisbon on day 13
current_day += cities[current_city]
itinerary.append({"flying": f"Day {current_day - cities[current_city]}-{current_day}", "from": current_city, "to": "Lisbon"})

current_city = "Lisbon"
current_day = current_day - cities[current_city] + 1  # Day 13
itinerary.append({"day_range": f"Day {current_day}-{current_day + cities[current_city] - 1}", "place": current_city})

# Flight from Lisbon to Naples on day 16
current_day += cities[current_city]
itinerary.append({"flying": f"Day {current_day - cities[current_city]}-{current_day}", "from": current_city, "to": "Naples"})

current_city = "Naples"
current_day = current_day - cities[current_city] + 1  # Day 16
itinerary.append({"day_range": f"Day {current_day}-{current_day + cities[current_city] - 1}", "place": current_city})

# Flight from Naples to Milan on day 19
current_day += cities[current_city]
itinerary.append({"flying": f"Day {current_day - cities[current_city]}-{current_day}", "from": current_city, "to": "Milan"})

current_city = "Milan"
current_day = current_day - cities[current_city] + 1  # Day 19
itinerary.append({"day_range": f"Day {current_day}-{current_day + cities[current_city] - 1}", "place": current_city})

# Flight from Milan to Santorini on day 22
current_day += cities[current_city]
itinerary.append({"flying": f"Day {current_day - cities[current_city]}-{current_day}", "from": current_city, "to": "Santorini"})

current_city = "Santorini"
current_day = current_day - cities[current_city] + 1  # Day 22
itinerary.append({"day_range": f"Day {current_day}-{current_day + cities[current_city] - 1}", "place": current_city})

# Flight from Santorini to Riga on day 27
current_day += cities[current_city]
itinerary.append({"flying": f"Day {current_day - cities[current_city]}-{current_day}", "from": current_city, "to": "Riga"})

current_city = "Riga"
current_day = current_day - cities[current_city] + 1  # Day 27
itinerary.append({"day_range": f"Day {current_day}-{current_day + cities[current_city] - 1}", "place": current_city})

# Output the itinerary as JSON
print(json.dumps(itinerary))