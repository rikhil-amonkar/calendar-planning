from z3 import *

# Define cities and their IDs
cities = ["Salzburg", "Venice", "Bucharest", "Brussels", "Hamburg", "Copenhagen", "Nice", "Zurich", "Naples"]
city_id = {city: idx for idx, city in enumerate(cities)}

# Direct flights (bidirectional)
direct_flights = [
    "Zurich and Brussels",
    "Bucharest and Copenhagen",
    "Venice and Brussels",
    "Nice and Zurich",
    "Hamburg and Nice",
    "Zurich and Naples",
    "Hamburg and Bucharest",
    "Zurich and Copenhagen",
    "Bucharest and Brussels",
    "Hamburg and Brussels",
    "Venice and Naples",
    "Venice and Copenhagen",
    "Bucharest and Naples",
    "Hamburg and Copenhagen",
    "Venice and Zurich",
    "Nice and Brussels",
    "Hamburg and Venice",
    "Copenhagen and Naples",
    "Nice and Naples",
    "Hamburg and Zurich",
    "Salzburg and Hamburg",
    "Zurich and Bucharest",
    "Brussels and Naples",
    "Copenhagen and Brussels",
    "Venice and Nice",
    "Nice and Copenhagen"
]

# Create flight pairs in both directions
flight_pairs = []
for flight in direct_flights:
    a, b = flight.split(" and ")
    a_id = city_id[a]
    b_id = city_id[b]
    flight_pairs.append((a_id, b_id))
    flight_pairs.append((b_id, a_id))

# Required days per city
required_days = {
    city_id["Salzburg"]: 2,
    city_id["Venice"]: 5,
    city_id["Bucharest"]: 4,
    city_id["Brussels"]: 2,
    city_id["Hamburg"]: 4,
    city_id["Copenhagen"]: 4,
    city_id["Nice"]: 3,
    city_id["Zurich"]: 5,
    city_id["Naples"]: 4
}

# Create solver
s = Solver()

# Day variables for 25 days (indices 0-24 correspond to days 1-25)
days = [Int(f'day_{i+1}') for i in range(25)]
for day in days:
    s.add(day >= 0, day < 9)  # Validate city IDs (0-8)

# Sum constraints for each city
for city in required_days:
    total = Sum([If(day == city, 1, 0) for day in days])
    s.add(total == required_days[city])

# Flight constraints between consecutive days
for i in range(24):
    current = days[i]
    next_day = days[i+1]
    constraints = [current == next_day]  # Stay in same city
    for a, b in flight_pairs:
        constraints.append(And(current == a, next_day == b))
    s.add(Or(constraints))

# Specific date constraints
brussels = city_id["Brussels"]
copenhagen = city_id["Copenhagen"]
nice = city_id["Nice"]
naples = city_id["Naples"]

# Brussels must be days 21-22 (indices 20-21)
s.add(days[20] == brussels)
s.add(days[21] == brussels)

# Copenhagen must be days 18-21 (indices 17-20)
for i in range(17, 21):
    s.add(days[i] == copenhagen)

# Nice must be days 9-11 (indices 8-10)
for i in range(8, 11):
    s.add(days[i] == nice)

# Naples must be days 22-25 (indices 21-24)
for i in range(21, 25):
    s.add(days[i] == naples)

# Check and print solution
if s.check() == sat:
    m = s.model()
    schedule = [m[day] for day in days]
    city_names = {v: k for k, v in city_id.items()}
    current_city = schedule[0]
    start_day = 1
    for i in range(1, 25):
        if schedule[i] != current_city:
            print(f"Days {start_day}-{i}: {city_names[current_city.as_long()]}")
            current_city = schedule[i]
            start_day = i + 1
    print(f"Days {start_day}-25: {city_names[current_city.as_long()]}")
else:
    print("No valid itinerary possible.")