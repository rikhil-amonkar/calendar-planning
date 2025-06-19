from z3 import *

# Define city names and their indices
cities = ["Copenhagen", "Geneva", "Mykonos", "Naples", "Prague", "Dubrovnik", "Athens", "Santorini", "Brussels", "Munich"]
n_cities = len(cities)

# Required days per city
days_req = [5, 3, 2, 4, 2, 3, 4, 5, 4, 5]

# Build the set of allowed transitions (direct flights and same city)
allowed_set = set()
# Add same city transitions
for i in range(n_cities):
    allowed_set.add((i, i))

# List of direct flights
flight_list = [
    "Copenhagen and Dubrovnik", "Brussels and Copenhagen", "Prague and Geneva", "Athens and Geneva",
    "Naples and Dubrovnik", "Athens and Dubrovnik", "Geneva and Mykonos", "Naples and Mykonos",
    "Naples and Copenhagen", "Munich and Mykonos", "Naples and Athens", "Prague and Athens",
    "Santorini and Geneva", "Athens and Santorini", "Naples and Munich", "Prague and Copenhagen",
    "Brussels and Naples", "Athens and Mykonos", "Athens and Copenhagen", "Naples and Geneva",
    "Dubrovnik and Munich", "Brussels and Munich", "Prague and Brussels", "Brussels and Athens",
    "Athens and Munich", "Geneva and Munich", "Copenhagen and Munich", "Brussels and Geneva",
    "Copenhagen and Geneva", "Prague and Munich", "Copenhagen and Santorini", "Naples and Santorini",
    "Geneva and Dubrovnik"
]

# Add direct flights to allowed_set
for flight in flight_list:
    parts = flight.split(" and ")
    city1 = parts[0]
    city2 = parts[1]
    idx1 = cities.index(city1)
    idx2 = cities.index(city2)
    allowed_set.add((idx1, idx2))
    allowed_set.add((idx2, idx1))

# Create Z3 solver
s = Solver()

# Use BitVec for city indices (4 bits sufficient for 10 cities)
schedule = [BitVec('s_%d' % i, 4) for i in range(28)]

# Constraint: each day variable is between 0 and 9 (city indices)
for i in range(28):
    s.add(And(schedule[i] >= 0, schedule[i] < n_cities))

# Constraint: total days per city
for city_idx in range(n_cities):
    total_days = Sum([If(schedule[i] == city_idx, 1, 0) for i in range(28)])
    s.add(total_days == days_req[city_idx])

# Constraint: Copenhagen must be visited between day 11 and 15 (indices 10 to 14)
s.add(Or([schedule[i] == 0 for i in [10, 11, 12, 13, 14]]))

# Constraint: Mykonos on day 27 and 28 (indices 26 and 27)
s.add(schedule[26] == 2)
s.add(schedule[27] == 2)

# Constraint: Naples between day 5 and 8 (indices 4 to 7)
s.add(Or([schedule[i] == 3 for i in [4, 5, 6, 7]]))

# Constraint: Athens between day 8 and 11 (indices 7 to 10)
s.add(Or([schedule[i] == 6 for i in [7, 8, 9, 10]]))

# Define a function for allowed transitions
def allowed_func(i, j):
    return Or([And(i == a, j == b) for (a, b) in allowed_set])

# Constraint: consecutive days must be allowed transitions
for i in range(27):
    s.add(allowed_func(schedule[i], schedule[i+1]))

# Solve the problem
if s.check() == sat:
    model = s.model()
    schedule_result = [model.evaluate(schedule[i]).as_long() for i in range(28)]
    for day in range(28):
        city_idx = schedule_result[day]
        print(f"Day {day+1}: {cities[city_idx]}")
else:
    print("No solution found")