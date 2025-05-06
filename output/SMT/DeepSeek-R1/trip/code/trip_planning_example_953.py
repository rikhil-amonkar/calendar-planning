from z3 import *

# Define cities and their IDs
cities = ["Salzburg", "Stockholm", "Venice", "Frankfurt", "Florence", "Barcelona", "Stuttgart"]
city_id = {city: idx for idx, city in enumerate(cities)}

# Direct flights (bidirectional)
direct_flights = [
    ("Barcelona", "Frankfurt"),
    ("Florence", "Frankfurt"),
    ("Stockholm", "Barcelona"),
    ("Barcelona", "Florence"),
    ("Venice", "Barcelona"),
    ("Stuttgart", "Barcelona"),
    ("Frankfurt", "Salzburg"),
    ("Stockholm", "Frankfurt"),
    ("Stuttgart", "Stockholm"),
    ("Stuttgart", "Frankfurt"),
    ("Venice", "Stuttgart"),
    ("Venice", "Frankfurt")
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
    city_id["Salzburg"]: 4,
    city_id["Stockholm"]: 2,
    city_id["Venice"]: 5,  # Typo in original problem? Should be "Venice"
    city_id["Frankfurt"]: 4,
    city_id["Florence"]: 4,
    city_id["Barcelona"]: 2,
    city_id["Stuttgart"]: 3
}

# Create solver
s = Solver()

# Day variables for 18 days (indices 0-17 correspond to days 1-18)
days = [Int(f'day_{i+1}') for i in range(18)]
for day in days:
    s.add(day >= 0, day < 7)  # Validate city IDs (0-6)

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

# Venice must be visited days 1-5 (indices 0-4)
venice_id = city_id["Venice"]
for i in range(5):
    s.add(days[i] == venice_id)

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