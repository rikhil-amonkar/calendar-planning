# Read the input parameters and flight connections
cities = {
    "Oslo": 2,
    "Helsinki": 2,
    "Edinburgh": 3,
    "Riga": 2,
    "Tallinn": 5,
    "Budapest": 5,
    "Vilnius": 5,
    "Porto": 5,
    "Geneva": 4
}

flights = {
    "Porto": ["Oslo"],
    "Edinburgh": ["Budapest", "Geneva"],
    "Riga": ["Tallinn"],
    "Edinburgh": ["Porto"],
    "Vilnius": ["Helsinki", "Budapest"],
    "Tallinn": ["Helsinki", "Vilnius"],
    "Riga": ["Oslo", "Helsinki"],
    "Geneva": ["Oslo", "Porto"],
    "Budapest": ["Geneva", "Oslo"],
    "Helsinki": ["Riga", "Vilnius", "Budapest", "Oslo"],
    "Oslo": ["Helsinki", "Riga", "Edinburgh", "Geneva"],
    "Edinburgh": ["Oslo", "Helsinki", "Riga", "Porto"],
    "Vilnius": ["Oslo", "Budapest"],
    "Porto": ["Edinburgh", "Geneva"],
    "Geneva": ["Porto", "Budapest"],
    "Budapest": ["Helsinki", "Geneva"],
    "Helsinki": ["Vilnius", "Tallinn", "Oslo", "Budapest"],
    "Tallinn": ["Oslo", "Vilnius"]
}

# Itinerary construction
itinerary = []

# Starting city
current_city = "Oslo"
current_day = 1
itinerary.append({"day_range": f"Day {current_day}-{current_day + cities[current_city] - 1}", "place": current_city})

# Flight from Oslo to Helsinki on day 2
current_day += cities[current_city]
itinerary.append({"flying": f"Day {current_day - cities[current_city]}-{current_day}", "from": current_city, "to": "Helsinki"})

current_city = "Helsinki"
current_day = current_day - cities[current_city] + 1  # Day 2
itinerary.append({"day_range": f"Day {current_day}-{current_day + cities[current_city] - 1}", "place": current_city})

# Flight from Helsinki to Riga on day 3
current_day += cities[current_city]
itinerary.append({"flying": f"Day {current_day - cities[current_city]}-{current_day}", "from": "Helsinki", "to": "Riga"})

current_city = "Riga"
current_day = current_day - cities[current_city] + 1  # Day 3
itinerary.append({"day_range": f"Day {current_day}-{current_day + cities[current_city] - 1}", "place": current_city})

# Flight from Riga to Tallinn on day 4
current_day += cities[current_city]
itinerary.append({"flying": f"Day {current_day - cities[current_city]}-{current_day}", "from": "Riga", "to": "Tallinn"})

current_city = "Tallinn"
current_day = current_day - cities[current_city] + 1  # Day 4
itinerary.append({"day_range": f"Day {current_day}-{current_day + cities[current_city] - 1}", "place": current_city})

# Flight from Tallinn to Vilnius on day 8
current_day += cities[current_city]
itinerary.append({"flying": f"Day {current_day - cities[current_city]}-{current_day}", "from": "Tallinn", "to": "Vilnius"})

current_city = "Vilnius"
current_day = current_day - cities[current_city] + 1  # Day 8
itinerary.append({"day_range": f"Day {current_day}-{current_day + cities[current_city] - 1}", "place": current_city})

# Flight from Vilnius to Budapest on day 12
current_day += cities[current_city]
itinerary.append({"flying": f"Day {current_day - cities[current_city]}-{current_day}", "from": "Vilnius", "to": "Budapest"})

current_city = "Budapest"
current_day = current_day - cities[current_city] + 1  # Day 12
itinerary.append({"day_range": f"Day {current_day}-{current_day + cities[current_city] - 1}", "place": current_city})

# Flight from Budapest to Geneva on day 16
current_day += cities[current_city]
itinerary.append({"flying": f"Day {current_day - cities[current_city]}-{current_day}", "from": "Budapest", "to": "Geneva"})

current_city = "Geneva"
current_day = current_day - cities[current_city] + 1  # Day 16
itinerary.append({"day_range": f"Day {current_day}-{current_day + cities[current_city] - 1}", "place": current_city})

# Flight from Geneva to Porto on day 19
current_day += cities[current_city]
itinerary.append({"flying": f"Day {current_day - cities[current_city]}-{current_day}", "from": "Geneva", "to": "Porto"})

current_city = "Porto"
current_day = current_day - cities[current_city] + 1  # Day 19
itinerary.append({"day_range": f"Day {current_day}-{current_day + cities[current_city] - 1}", "place": current_city})

# Flight from Porto to Edinburgh on day 23
current_day += cities[current_city]
itinerary.append({"flying": f"Day {current_day - cities[current_city]}-{current_day}", "from": "Porto", "to": "Edinburgh"})

current_city = "Edinburgh"
current_day = current_day - cities[current_city] + 1  # Day 23
itinerary.append({"day_range": f"Day {current_day}-{current_day + cities[current_city] - 1}", "place": current_city})

# Output the itinerary as JSON
print(json.dumps(itinerary))