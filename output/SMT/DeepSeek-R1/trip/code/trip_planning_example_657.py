from z3 import *

# Define cities and their IDs
cities = ["Frankfurt", "Manchester", "Valencia", "Naples", "Oslo", "Vilnius"]
city_id = {city: idx for idx, city in enumerate(cities)}

# Direct flights (bidirectional)
direct_flights = [
    ("Valencia", "Frankfurt"),
    ("Manchester", "Frankfurt"),
    ("Naples", "Manchester"),
    ("Naples", "Frankfurt"),
    ("Naples", "Oslo"),
    ("Oslo", "Frankfurt"),
    ("Vilnius", "Frankfurt"),
    ("Oslo", "Vilnius"),
    ("Manchester", "Oslo"),
    ("Valencia", "Naples")
]

# Create flight pairs in both directions
flight_pairs = []
for a, b in direct_flights:
    a_id = city_id[a]
    b_id = city_id[b]
    flight_pairs.append((a_id, b_id))
    flight_pairs.append((b_id, a_id))

# Required days per city
required_days = {
    city_id["Frankfurt"]: 4,
    city_id["Manchester"]: 4,
    city_id["Valencia"]: 4,
    city_id["Naples"]: 4,
    city_id["Oslo"]: 3,
    city_id["Vilnius"]: 2
}

# Create solver
s = Solver()

# Day variables: 16 days (indices 0-15 correspond to days 1-16)
days = [Int(f'day_{i+1}') for i in range(16)]
for day in days:
    s.add(day >= 0, day < 6)  # Validate city IDs (0-5)

# Sum constraints for each city
for city in required_days:
    total = Sum([If(day == city, 1, 0) for day in days])
    s.add(total == required_days[city])

# Flight constraints between consecutive days
for i in range(15):
    current = days[i]
    next_day = days[i+1]
    constraints = [current == next_day]  # Stay in same city
    for a, b in flight_pairs:
        constraints.append(And(current == a, next_day == b))
    s.add(Or(constraints))

# Specific date constraints
frankfurt = city_id["Frankfurt"]
vilnius = city_id["Vilnius"]

# Frankfurt must be days 13-16 (indices 12-15)
for i in range(12, 16):
    s.add(days[i] == frankfurt)

# Vilnius must be days 12-13 (indices 11-12)
s.add(days[11] == vilnius)
s.add(days[12] == vilnius)

# Check and print solution
if s.check() == sat:
    m = s.model()
    schedule = [m[day] for day in days]
    city_names = {v: k for k, v in city_id.items()}
    current_city = schedule[0]
    start_day = 1
    for i in range(1, 16):
        if schedule[i] != current_city:
            print(f"Days {start_day}-{i}: {city_names[current_city.as_long()]}")
            current_city = schedule[i]
            start_day = i + 1
    print(f"Days {start_day}-16: {city_names[current_city.as_long()]}")
else:
    print("No valid itinerary possible.")