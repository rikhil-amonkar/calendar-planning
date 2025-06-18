from z3 import *

# Define city names
cities = ["Copenhagen", "Geneva", "Mykonos", "Naples", "Prague", "Dubrovnik", "Athens", "Santorini", "Brussels", "Munich"]
n_cities = len(cities)

# Required days per city
days_req = [5, 3, 2, 4, 2, 3, 4, 5, 4, 5]

# Create an enumeration sort for cities
City, (Copenhagen, Geneva, Mykonos, Naples, Prague, Dubrovnik, Athens, Santorini, Brussels, Munich) = EnumSort('City', cities)

# Map city names to enum constants
city_constants = [Copenhagen, Geneva, Mykonos, Naples, Prague, Dubrovnik, Athens, Santorini, Brussels, Munich]

# Build the set of allowed transitions (direct flights and same city)
allowed_transitions = set()
# Add same city transitions
for city in city_constants:
    allowed_transitions.add((city, city))

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

# Add direct flights to allowed transitions
for flight in flight_list:
    city1, city2 = flight.split(" and ")
    idx1 = cities.index(city1)
    idx2 = cities.index(city2)
    allowed_transitions.add((city_constants[idx1], city_constants[idx2]))
    allowed_transitions.add((city_constants[idx2], city_constants[idx1]))

# Create Z3 solver
s = Solver()

# Create 28 variables for the schedule
schedule = [Const('s_%d' % i, City) for i in range(28)]

# Constraint: total days per city
for idx, city in enumerate(city_constants):
    total_days = Sum([If(schedule[i] == city, 1, 0) for i in range(28)])
    s.add(total_days == days_req[idx])

# Constraint: Copenhagen between day 11 and 15 (indices 10 to 14)
s.add(Or([schedule[i] == Copenhagen for i in [10, 11, 12, 13, 14]]))

# Constraint: Mykonos on day 27 and 28 (indices 26 and 27)
s.add(schedule[26] == Mykonos)
s.add(schedule[27] == Mykonos)

# Constraint: Naples between day 5 and 8 (indices 4 to 7)
s.add(Or([schedule[i] == Naples for i in [4, 5, 6, 7]]))

# Constraint: Athens between day 8 and 11 (indices 7 to 10)
s.add(Or([schedule[i] == Athens for i in [7, 8, 9, 10]]))

# Constraint: consecutive days must be allowed transitions
for i in range(27):
    s.add(Or([And(schedule[i] == a, schedule[i+1] == b) for (a, b) in allowed_transitions]))

# Solve the problem
if s.check() == sat:
    m = s.model()
    schedule_result = [m.evaluate(schedule[i]) for i in range(28)]
    for day in range(28):
        city_index = city_constants.index(schedule_result[day])
        print(f"Day {day+1}: {cities[city_index]}")
else:
    print("No solution found")