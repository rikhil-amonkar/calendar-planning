import json

# Define the required stays for each city
required_stays = {
    "Vienna": 4,
    "Milan": 2,
    "Vilnius": 4,
    "Riga": 2,
    "Rome": 3,
    "Lisbon": 3,
    "Oslo": 3
}

# Define direct flights as a set of tuples (bidirectional)
direct_flights = {
    ("Riga", "Oslo"),
    ("Rome", "Oslo"),
    ("Vienna", "Milan"),
    ("Vienna", "Vilnius"),
    ("Vienna", "Lisbon"),
    ("Riga", "Milan"),
    ("Lisbon", "Oslo"),
    ("Rome", "Riga"),
    ("Rome", "Lisbon"),
    ("Vienna", "Riga"),
    ("Vienna", "Rome"),
    ("Milan", "Oslo"),
    ("Vienna", "Oslo"),
    ("Vilnius", "Oslo"),
    ("Riga", "Vilnius"),
    ("Vilnius", "Milan"),
    ("Riga", "Lisbon"),
    ("Milan", "Lisbon"),
    # Add reverse tuples for bidirectional flights
    ("Oslo", "Riga"),
    ("Oslo", "Rome"),
    ("Milan", "Vienna"),
    ("Vilnius", "Vienna"),
    ("Lisbon", "Vienna"),
    ("Milan", "Riga"),
    ("Oslo", "Lisbon"),
    ("Riga", "Rome"),
    ("Lisbon", "Rome"),
    ("Riga", "Vienna"),
    ("Rome", "Vienna"),
    ("Oslo", "Milan"),
    ("Oslo", "Vienna"),
    ("Oslo", "Vilnius"),
    ("Vilnius", "Riga"),
    ("Milan", "Vilnius"),
    ("Lisbon", "Riga"),
    ("Lisbon", "Milan"),
}

# Initialize the itinerary
itinerary = []
current_day = 1

# Add Vienna
itinerary.append({"day_range": f"Day {current_day}-{current_day + required_stays['Vienna'] - 1}", "place": "Vienna"})
current_day = current_day + required_stays["Vienna"] - 1  # Next start day is the last day of Vienna

# Add Milan
itinerary.append({"day_range": f"Day {current_day}-{current_day + required_stays['Milan'] - 1}", "place": "Milan"})
current_day = current_day + required_stays["Milan"] - 1

# Add Vilnius
itinerary.append({"day_range": f"Day {current_day}-{current_day + required_stays['Vilnius'] - 1}", "place": "Vilnius"})
current_day = current_day + required_stays["Vilnius"] - 1

# Add Riga
itinerary.append({"day_range": f"Day {current_day}-{current_day + required_stays['Riga'] - 1}", "place": "Riga"})
current_day = current_day + required_stays["Riga"] - 1

# Add Rome
itinerary.append({"day_range": f"Day {current_day}-{current_day + required_stays['Rome'] - 1}", "place": "Rome"})
current_day = current_day + required_stays["Rome"] - 1

# Add Lisbon
itinerary.append({"day_range": f"Day {current_day}-{current_day + required_stays['Lisbon'] - 1}", "place": "Lisbon"})
current_day = current_day + required_stays["Lisbon"] - 1

# Add Oslo
itinerary.append({"day_range": f"Day {current_day}-{current_day + required_stays['Oslo'] - 1}", "place": "Oslo"})
current_day = current_day + required_stays["Oslo"] - 1

# Check that all direct flights are valid
itinerary_cities = [item["place"] for item in itinerary]
valid = True
for i in range(len(itinerary_cities) - 1):
    city_a = itinerary_cities[i]
    city_b = itinerary_cities[i+1]
    if (city_a, city_b) not in direct_flights:
        valid = False
        break

if not valid:
    raise ValueError("Invalid itinerary: missing direct flight")

# Output as JSON
result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))