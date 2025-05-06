from z3 import *

# Define cities and their IDs
cities = ["Prague", "Tallinn", "Warsaw", "Porto", "Naples", "Milan", "Lisbon", "Santorini", "Riga", "Stockholm"]
city_id = {city: idx for idx, city in enumerate(cities)}

# Direct flights (parse directional and bidirectional)
direct_flights = [
    "Riga and Prague",
    "Stockholm and Milan",
    "Riga and Milan",
    "Lisbon and Stockholm",
    "from Stockholm to Santorini",
    "Naples and Warsaw",
    "Lisbon and Warsaw",
    "Naples and Milan",
    "Lisbon and Naples",
    "from Riga to Tallinn",
    "Tallinn and Prague",
    "Stockholm and Warsaw",
    "Riga and Warsaw",
    "Lisbon and Riga",
    "Riga and Stockholm",
    "Lisbon and Porto",
    "Lisbon and Prague",
    "Milan and Porto",
    "Prague and Milan",
    "Lisbon and Milan",
    "Warsaw and Porto",
    "Warsaw and Tallinn",
    "Santorini and Milan",
    "Stockholm and Prague",
    "Stockholm and Tallinn",
    "Warsaw and Milan",
    "Santorini and Naples",
    "Warsaw and Prague"
]

# Parse flight pairs (bidirectional or directional)
flight_pairs = []
for flight in direct_flights:
    if flight.startswith("from"):
        parts = flight.split()
        a = parts[1]
        b = parts[3]
        a_id = city_id[a]
        b_id = city_id[b]
        flight_pairs.append((a_id, b_id))
    else:
        cities_flight = flight.split(" and ")
        a = cities_flight[0]
        b = cities_flight[1]
        a_id = city_id[a]
        b_id = city_id[b]
        flight_pairs.append((a_id, b_id))
        flight_pairs.append((b_id, a_id))

# Required days per city
required_days = {
    city_id["Prague"]: 5,
    city_id["Tallinn"]: 3,
    city_id["Warsaw"]: 2,
    city_id["Porto"]: 3,
    city_id["Naples"]: 5,
    city_id["Milan"]: 3,
    city_id["Lisbon"]: 5,
    city_id["Santorini"]: 5,
    city_id["Riga"]: 4,
    city_id["Stockholm"]: 2
}

# Create solver
s = Solver()

# Day variables: 0-based for 28 days (days 1-28)
days = [Int(f'day_{i+1}') for i in range(28)]
for day in days:
    s.add(day >= 0, day < 10)  # Validate city IDs (0-9)

# Sum constraints for each city
for city in required_days:
    total = Sum([If(day == city, 1, 0) for day in days])
    s.add(total == required_days[city])

# Flight constraints between consecutive days
for i in range(27):
    current = days[i]
    next_day = days[i+1]
    constraints = [current == next_day]  # Stay in same city
    for a, b in flight_pairs:
        constraints.append(And(current == a, next_day == b))
    s.add(Or(constraints))

# Specific date constraints
tallinn = city_id["Tallinn"]
milan = city_id["Milan"]
riga = city_id["Riga"]

# Tallinn between days 18-20 (indices 17-19)
for i in range(17, 20):
    s.add(days[i] == tallinn)

# Milan between days 24-26 (indices 23-25)
for i in range(23, 26):
    s.add(days[i] == milan)

# Riga between days 5-8 (indices 4-7)
for i in range(4, 8):
    s.add(days[i] == riga)

# Check and print solution
if s.check() == sat:
    m = s.model()
    schedule = [m[day] for day in days]
    city_names = {v: k for k, v in city_id.items()}
    current_city = schedule[0]
    start_day = 1
    for i in range(1, 28):
        if schedule[i] != current_city:
            print(f"Days {start_day}-{i}: {city_names[current_city.as_long()]}")
            current_city = schedule[i]
            start_day = i + 1
    print(f"Days {start_day}-28: {city_names[current_city.as_long()]}")
else:
    print("No valid itinerary possible.")