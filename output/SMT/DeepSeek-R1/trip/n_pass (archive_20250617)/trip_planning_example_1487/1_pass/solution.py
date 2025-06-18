from z3 import *

# Define city names and their indices
cities = ["Copenhagen", "Geneva", "Mykonos", "Naples", "Prague", "Dubrovnik", "Athens", "Santorini", "Brussels", "Munich"]
n_cities = len(cities)

# Required days per city: [Copenhagen, Geneva, Mykonos, Naples, Prague, Dubrovnik, Athens, Santorini, Brussels, Munich]
days_req = [5, 3, 2, 4, 2, 3, 4, 5, 4, 5]

# Build the set of allowed transitions (direct flights and same city)
allowed_transitions = set()
# Add same city transitions (stay in the same city)
for i in range(n_cities):
    allowed_transitions.add((i, i))

# List of direct flights
flight_list = [
    "Copenhagen and Dubrovnik",
    "Brussels and Copenhagen",
    "Prague and Geneva",
    "Athens and Geneva",
    "Naples and Dubrovnik",
    "Athens and Dubrovnik",
    "Geneva and Mykonos",
    "Naples and Mykonos",
    "Naples and Copenhagen",
    "Munich and Mykonos",
    "Naples and Athens",
    "Prague and Athens",
    "Santorini and Geneva",
    "Athens and Santorini",
    "Naples and Munich",
    "Prague and Copenhagen",
    "Brussels and Naples",
    "Athens and Mykonos",
    "Athens and Copenhagen",
    "Naples and Geneva",
    "Dubrovnik and Munich",
    "Brussels and Munich",
    "Prague and Brussels",
    "Brussels and Athens",
    "Athens and Munich",
    "Geneva and Munich",
    "Copenhagen and Munich",
    "Brussels and Geneva",
    "Copenhagen and Geneva",
    "Prague and Munich",
    "Copenhagen and Santorini",
    "Naples and Santorini",
    "Geneva and Dubrovnik"
]

# Map flight strings to city indices and add both directions to allowed_transitions
for flight in flight_list:
    parts = flight.split(" and ")
    city1 = parts[0]
    city2 = parts[1]
    idx1 = cities.index(city1)
    idx2 = cities.index(city2)
    allowed_transitions.add((idx1, idx2))
    allowed_transitions.add((idx2, idx1))

# Create Z3 solver
s = Solver()

# Create 28 integer variables for the schedule (days 1 to 28)
schedule = [Int('s_%d' % i) for i in range(28)]

# Constraint: each day variable is between 0 and 9 (city indices)
for i in range(28):
    s.add(schedule[i] >= 0, schedule[i] < n_cities)

# Constraint: total days per city
for city_idx in range(n_cities):
    total_days = Sum([If(schedule[i] == city_idx, 1, 0) for i in range(28)])
    s.add(total_days == days_req[city_idx])

# Constraint: Copenhagen must be visited between day 11 and 15 (days 11,12,13,14,15 -> indices 10 to 14)
s.add(Or([schedule[i] == 0 for i in [10, 11, 12, 13, 14]]))

# Constraint: Mykonos on day 27 and 28 (indices 26 and 27)
s.add(schedule[26] == 2)  # Mykonos index is 2
s.add(schedule[27] == 2)

# Constraint: Naples between day 5 and 8 (days 5,6,7,8 -> indices 4,5,6,7)
s.add(Or([schedule[i] == 3 for i in [4, 5, 6, 7]]))  # Naples index is 3

# Constraint: Athens between day 8 and 11 (days 8,9,10,11 -> indices 7,8,9,10)
s.add(Or([schedule[i] == 6 for i in [7, 8, 9, 10]]))  # Athens index is 6

# Constraint: consecutive days must be either the same city or connected by a direct flight
for i in range(27):
    # Create a disjunction for all allowed transitions (a, b) such that (schedule[i], schedule[i+1]) is in allowed_transitions
    disj = []
    for (a, b) in allowed_transitions:
        disj.append(And(schedule[i] == a, schedule[i+1] == b))
    s.add(Or(disj))

# Solve the problem
if s.check() == sat:
    model = s.model()
    schedule_result = [model.evaluate(schedule[i]).as_long() for i in range(28)]
    # Print the schedule
    for day in range(28):
        city_idx = schedule_result[day]
        print(f"Day {day+1}: {cities[city_idx]}")
else:
    print("No solution found")