from z3 import *
import json

# Define cities and their durations
cities = ["Dublin", "Madrid", "Oslo", "London", "Vilnius", "Berlin"]
city_to_index = {city: i for i, city in enumerate(cities)}
city_durations = [3, 2, 3, 2, 3, 5]  # Dublin, Madrid, Oslo, London, Vilnius, Berlin

# Define direct flight connections
direct_flights = {
    ("London", "Madrid"),
    ("Oslo", "Vilnius"),
    ("Berlin", "Vilnius"),
    ("Madrid", "Oslo"),
    ("Madrid", "Dublin"),
    ("London", "Oslo"),
    ("Madrid", "Berlin"),
    ("Berlin", "Oslo"),
    ("Dublin", "Oslo"),
    ("London", "Dublin"),
    ("London", "Berlin"),
    ("Berlin", "Dublin")
}

# Generate allowed transitions as pairs of city indices
allowed_transitions = []
for (c1, c2) in direct_flights:
    allowed_transitions.append((city_to_index[c1], city_to_index[c2]))
    allowed_transitions.append((city_to_index[c2], city_to_index[c1]))
allowed_transitions = list(set(allowed_transitions))  # Remove duplicates

# Initialize Z3 solver
s = Solver()

# Variables for city order
cities_order = [Int(f"order_{i}") for i in range(6)]

# Constraints for city order: all distinct and in 0-5
s.add(Distinct(cities_order))
for i in range(6):
    s.add(And(cities_order[i] >= 0, cities_order[i] <= 5))

# Constraints for allowed transitions between consecutive cities
for i in range(5):
    current = cities_order[i]
    next_city = cities_order[i + 1]
    constraints = []
    for (a, b) in allowed_transitions:
        constraints.append(And(current == a, next_city == b))
    s.add(Or(constraints))

# Variables for start and end days
start_days = [Int(f"start_{i}") for i in range(6)]
end_days = [Int(f"end_{i}") for i in range(6)]

# First day starts at 1
s.add(start_days[0] == 1)

# End day for each city is start + duration - 1
for i in range(6):
    duration = If(cities_order[i] == 0, 3,
                  If(cities_order[i] == 1, 2,
                     If(cities_order[i] == 2, 3,
                        If(cities_order[i] == 3, 2,
                           If(cities_order[i] == 4, 3, 5))))
    s.add(end_days[i] == start_days[i] + duration - 1)

# Consecutive cities share the same start/end day
for i in range(5):
    s.add(start_days[i + 1] == end_days[i])

# Last day of the trip is day 13
s.add(end_days[5] == 13)

# Per-city day constraints
for i in range(6):
    # Dublin (index 0): start between 5 and 9
    s.add(Implies(cities_order[i] == 0, And(start_days[i] >= 5, start_days[i] <= 9)))
    # Madrid (index 1): start between 1 and 3
    s.add(Implies(cities_order[i] == 1, And(start_days[i] >= 1, start_days[i] <= 3)))
    # Berlin (index 5): start between 1 and 7
    s.add(Implies(cities_order[i] == 5, And(start_days[i] >= 1, start_days[i] <= 7)))

# Check for solution
if s.check() == sat:
    model = s.model()
    # Extract city order, start, and end days
    order = [model.evaluate(cities_order[i]).as_long() for i in range(6)]
    starts = [model.evaluate(start_days[i]).as_long() for i in range(6)]
    ends = [model.evaluate(end_days[i]).as_long() for i in range(6)]
    
    # Build the itinerary
    itinerary = []
    for i in range(6):
        city_name = cities[order[i]]
        day_range = f"Day {starts[i]}-{ends[i]}"
        itinerary.append({"day_range": day_range, "place": city_name})
    
    # Output as JSON
    print(json.dumps({"itinerary": itinerary}))
else:
    print("No solution found.")