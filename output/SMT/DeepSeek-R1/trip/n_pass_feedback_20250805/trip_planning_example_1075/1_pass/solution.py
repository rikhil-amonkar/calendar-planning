import json
from z3 import *

# Define the cities and their indices
cities = {
    "Vienna": 0,
    "Lyon": 1,
    "Edinburgh": 2,
    "Reykjavik": 3,
    "Stuttgart": 4,
    "Manchester": 5,
    "Split": 6,
    "Prague": 7
}
city_names = {v: k for k, v in cities.items()}

# Define the direct flight graph (undirected)
graph = {
    0: [4, 7, 5, 1, 3, 6],  # Vienna
    1: [0, 6, 7],             # Lyon
    2: [7, 4],                # Edinburgh
    3: [4, 0, 7],             # Reykjavik
    4: [3, 6, 0, 2, 5],       # Stuttgart
    5: [7, 6, 0, 4],          # Manchester
    6: [4, 5, 7, 1, 0],       # Split
    7: [5, 2, 0, 6, 1, 3]     # Prague
}

# Create directed edges (both directions for undirected graph)
directed_edges = []
for a, neighbors in graph.items():
    for b in neighbors:
        directed_edges.append((a, b))

# Initialize Z3 solver
s = Solver()

# Define variables: current_city[0] to current_city[25]
current_city = [Int(f'current_city_{i}') for i in range(26)]
# Define stay flags for days 1 to 25
stay = [Bool(f'stay_{i}') for i in range(1, 26)]

# Constraint: current_city values are between 0 and 7
for i in range(26):
    s.add(current_city[i] >= 0, current_city[i] < 8)

# Constraints for each day from 1 to 25
for i in range(1, 26):
    # If stay[i-1] is True, then current_city[i] must equal current_city[i-1]
    s.add(Implies(stay[i-1], current_city[i] == current_city[i-1]))
    
    # If not staying, then the flight (current_city[i-1] to current_city[i]) must be a directed edge
    flight_options = []
    for a, b in directed_edges:
        flight_options.append(And(current_city[i-1] == a, current_city[i] == b))
    s.add(Implies(Not(stay[i-1]), Or(flight_options)))

# Define in_city function for day i and city c
def in_city(i, c):
    return Or(current_city[i-1] == c, And(Not(stay[i-1]), current_city[i] == c))

# Total days per city constraints
total_days = [0] * 8
for c in range(8):
    total = 0
    for i in range(1, 26):
        total += If(in_city(i, c), 1, 0)
    total_days[c] = total

s.add(total_days[0] == 4)  # Vienna
s.add(total_days[1] == 3)  # Lyon
s.add(total_days[2] == 4)  # Edinburgh
s.add(total_days[3] == 5)  # Reykjavik
s.add(total_days[4] == 5)  # Stuttgart
s.add(total_days[5] == 2)  # Manchester
s.add(total_days[6] == 5)  # Split
s.add(total_days[7] == 4)  # Prague

# Edinburgh must be visited on days 5-8 and not on any other day
for i in range(1, 5):  # Days 1-4
    s.add(Not(in_city(i, 2)))
for i in range(5, 9):  # Days 5-8
    s.add(in_city(i, 2))
for i in range(9, 26):  # Days 9-25
    s.add(Not(in_city(i, 2)))

# Split must be visited at least once between days 19-23
split_days = []
for i in [19, 20, 21, 22, 23]:
    split_days.append(in_city(i, 6))
s.add(Or(split_days))

# Check if a solution exists
if s.check() == sat:
    model = s.model()
    itinerary = []
    for day in range(1, 26):
        places = []
        for c in range(8):
            cond = in_city(day, c)
            if is_true(model.eval(cond)):
                places.append(city_names[c])
        itinerary.append({"day": day, "place": places})
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    print("No solution found")