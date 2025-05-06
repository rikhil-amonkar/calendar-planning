from z3 import *

# Define cities and their IDs
cities = ["Split", "Helsinki", "Reykjavik", "Vilnius", "Geneva"]
city_id = {city: idx for idx, city in enumerate(cities)}

# Direct flights (bidirectional)
direct_flights = [
    ("Split", "Helsinki"),
    ("Geneva", "Split"),
    ("Geneva", "Helsinki"),
    ("Helsinki", "Reykjavik"),
    ("Vilnius", "Helsinki"),
    ("Split", "Vilnius")
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
    city_id["Split"]: 2,
    city_id["Helsinki"]: 2,
    city_id["Reykjavik"]: 3,
    city_id["Vilnius"]: 3,
    city_id["Geneva"]: 6
}

# Create solver
s = Solver()

# Day variables: 12 days (indices 0-11 correspond to days 1-12)
days = [Int(f'day_{i+1}') for i in range(12)]
for day in days:
    s.add(day >= 0, day < 5)  # City IDs 0-4

# Sum constraints for each city
for city in required_days:
    total = Sum([If(day == city, 1, 0) for day in days])
    s.add(total == required_days[city])

# Flight constraints between consecutive days
for i in range(11):
    current = days[i]
    next_day = days[i+1]
    constraints = [current == next_day]  # Stay in same city
    for a, b in flight_pairs:
        constraints.append(And(current == a, next_day == b))
    s.add(Or(constraints))

# Specific constraints
reykjavik = city_id["Reykjavik"]
vilnius = city_id["Vilnius"]

# Reykjavik must be visited between days 10-12 (indices 9-11)
for i in range(9, 12):
    s.add(days[i] == reykjavik)

# Vilnius must be visited between days 7-9 (indices 6-8)
vilnius_days = [days[i] == vilnius for i in range(6, 9)]
s.add(Or(vilnius_days))  # At least one day in Vilnius during this period

# Check and print solution
if s.check() == sat:
    m = s.model()
    schedule = [m[day] for day in days]
    city_names = {v: k for k, v in city_id.items()}
    current_city = schedule[0]
    start_day = 1
    for i in range(1, 12):
        if schedule[i] != current_city:
            print(f"Days {start_day}-{i}: {city_names[current_city.as_long()]}")
            current_city = schedule[i]
            start_day = i + 1
    print(f"Days {start_day}-12: {city_names[current_city.as_long()]}")
else:
    print("No valid itinerary possible.")