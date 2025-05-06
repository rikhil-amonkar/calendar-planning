from z3 import *

# Define cities and their IDs
cities = ["Dublin", "Helsinki", "Riga", "Reykjavik", "Vienna", "Tallinn"]
city_id = {city: idx for idx, city in enumerate(cities)}

# Direct flights (bidirectional)
direct_flights = [
    ("Helsinki", "Riga"),
    ("Riga", "Tallinn"),
    ("Riga", "Vienna"),
    ("Riga", "Helsinki"),
    ("Riga", "Dublin"),
    ("Vienna", "Riga"),
    ("Reykjavik", "Vienna"),
    ("Helsinki", "Dublin"),
    ("Tallinn", "Dublin"),
    ("Reykjavik", "Helsinki"),
    ("Reykjavik", "Dublin"),
    ("Helsinki", "Tallinn"),
    ("Vienna", "Dublin")
]

# Create flight pairs in both directions
flight_pairs = []
for a, b in direct_flights:
    flight_pairs.append((city_id[a], city_id[b]))
    flight_pairs.append((city_id[b], city_id[a]))

# Required days per city
required_days = {
    city_id["Dublin"]: 5,
    city_id["Helsinki"]: 3,
    city_id["Riga"]: 3,
    city_id["Reykjavik"]: 2,
    city_id["Vienna"]: 2,
    city_id["Tallinn"]: 5
}

# Create solver
s = Solver()

# Day variables: day 0 to day 14 (representing days 1 to 15)
days = [Int(f'day_{i+1}') for i in range(15)]
for day in days:
    s.add(day >= 0, day < 6)  # Each day must be a valid city ID

# Sum constraints for each city
for city in required_days:
    total = Sum([If(day == city, 1, 0) for day in days])
    s.add(total == required_days[city])

# Flight constraints between consecutive days
for i in range(14):
    current = days[i]
    next_c = days[i+1]
    # Either stay in the same city or fly directly
    constraints = [current == next_c]
    for a, b in flight_pairs:
        constraints.append(And(current == a, next_c == b))
    s.add(Or(constraints))

# Specific constraints
vienna = city_id["Vienna"]
helsinki = city_id["Helsinki"]
tallinn = city_id["Tallinn"]

# Days 2 and 3 must be Vienna (indices 1 and 2)
s.add(days[1] == vienna)
s.add(days[2] == vienna)

# Helsinki must have at least one day between days 3-5 (indices 2,3,4)
s.add(Or(days[2] == helsinki, days[3] == helsinki, days[4] == helsinki))

# Tallinn must have at least one day between days 7-11 (indices 6 to 10)
tallinn_days = [days[i] == tallinn for i in range(6, 11)]
s.add(Or(tallinn_days))

# Check and print solution
if s.check() == sat:
    m = s.model()
    schedule = [m[day] for day in days]
    city_names = {v: k for k, v in city_id.items()}
    current_city = schedule[0]
    start_day = 1
    for i in range(1, 15):
        if schedule[i] != current_city:
            print(f"Days {start_day}-{i}: {city_names[current_city.as_long()]}")
            current_city = schedule[i]
            start_day = i + 1
    print(f"Days {start_day}-15: {city_names[current_city.as_long()]}")
else:
    print("No valid itinerary possible.")