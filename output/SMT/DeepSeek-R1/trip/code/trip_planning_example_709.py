from z3 import *

# Define cities and their IDs
cities = ["Helsinki", "Valencia", "Dubrovnik", "Porto", "Prague", "Reykjavik"]
city_id = {city: idx for idx, city in enumerate(cities)}

# Direct flights (bidirectional)
direct_flights = [
    ("Helsinki", "Prague"),
    ("Prague", "Valencia"),
    ("Valencia", "Porto"),
    ("Helsinki", "Reykjavik"),
    ("Dubrovnik", "Helsinki"),
    ("Reykjavik", "Prague")
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
    city_id["Helsinki"]: 4,
    city_id["Valencia"]: 5,
    city_id["Dubrovnik"]: 4,
    city_id["Porto"]: 3,
    city_id["Prague"]: 3,
    city_id["Reykjavik"]: 4
}

# Create solver
s = Solver()

# Day variables: 18 days (indices 0-17 correspond to days 1-18)
days = [Int(f'day_{i+1}') for i in range(18)]
for day in days:
    s.add(day >= 0, day < 6)  # Validate city IDs (0-5)

# Sum constraints for each city
for city in required_days:
    total = Sum([If(day == city, 1, 0) for day in days])
    s.add(total == required_days[city])

# Flight constraints between consecutive days
for i in range(17):
    current = days[i]
    next_day = days[i+1]
    constraints = [current == next_day]  # Stay in same city
    for a, b in flight_pairs:
        constraints.append(And(current == a, next_day == b))
    s.add(Or(constraints))

# Porto must be days 16-18 (indices 15-17)
porto = city_id["Porto"]
for i in range(15, 18):
    s.add(days[i] == porto)

# Check and print solution
if s.check() == sat:
    m = s.model()
    schedule = [m[day] for day in days]
    city_names = {v: k for k, v in city_id.items()}
    current_city = schedule[0]
    start_day = 1
    for i in range(1, 18):
        if schedule[i] != current_city:
            print(f"Days {start_day}-{i}: {city_names[current_city.as_long()]}")
            current_city = schedule[i]
            start_day = i + 1
    print(f"Days {start_day}-18: {city_names[current_city.as_long()]}")
else:
    print("No valid itinerary possible.")