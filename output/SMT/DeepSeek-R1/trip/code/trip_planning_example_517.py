from z3 import *

# Define the cities and their integer representations
cities = {
    "Bucharest": 0,
    "Stuttgart": 1,
    "Dubrovnik": 2,
    "Warsaw": 3,
    "Copenhagen": 4
}

# Direct flights represented as adjacency list (each city has a list of directly connected cities)
direct_flights = {
    cities["Bucharest"]: [cities["Copenhagen"], cities["Warsaw"]],
    cities["Stuttgart"]: [cities["Copenhagen"], cities["Warsaw"]],
    cities["Dubrovnik"]: [cities["Copenhagen"]],
    cities["Warsaw"]: [cities["Copenhagen"], cities["Stuttgart"], cities["Bucharest"]],
    cities["Copenhagen"]: [cities["Warsaw"], cities["Stuttgart"], cities["Bucharest"], cities["Dubrovnik"]]
}

# Create solver and day variables (days 1 to 19)
s = Solver()
days = [Int(f'day_{i}') for i in range(1, 20)]

# Each day must be one of the cities
for d in days:
    s.add(Or([d == city for city in cities.values()]))

# Constraints for Bucharest (days 1-6)
for i in range(6):
    s.add(days[i] == cities["Bucharest"])

# Stuttgart must be visited on day 7 and 13
s.add(days[6] == cities["Stuttgart"])  # day 7 is index 6
s.add(days[12] == cities["Stuttgart"]) # day 13 is index 12

# Valid transitions between consecutive days (direct flights)
for i in range(18):
    current = days[i]
    next_day = days[i+1]
    s.add(Or([And(current == src, next_day == dst) for src in direct_flights for dst in direct_flights[src]]))

# Count constraints for each city
city_counts = [
    (cities["Dubrovnik"], 5),
    (cities["Warsaw"], 2),
    (cities["Stuttgart"], 7),
    (cities["Bucharest"], 6),
    (cities["Copenhagen"], 3)
]

for city, count in city_counts:
    s.add(Sum([If(d == city, 1, 0) for d in days]) == count)

# Check and print the solution
if s.check() == sat:
    m = s.model()
    schedule = [m[d] for d in days]
    city_names = {v: k for k, v in cities.items()}
    for idx, city_num in enumerate(schedule, 1):
        print(f"Day {idx}: {city_names[city_num.as_long()]}")
else:
    print("No valid trip plan exists.")