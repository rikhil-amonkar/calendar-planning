from z3 import *
import json

# Define cities and their indices
cities = ["Rome", "Mykonos", "Lisbon", "Frankfurt", "Nice", "Stuttgart", "Venice", "Dublin", "Bucharest", "Seville"]
city_to_idx = {city: i for i, city in enumerate(cities)}

# Define durations for each city (index 0 to 9)
durations_list = [3, 2, 2, 5, 3, 4, 4, 2, 2, 5]

# Helper function to get duration of a city given by a symbolic index
def get_duration(city_idx):
    return If(city_idx == 0, 3,
              If(city_idx == 1, 2,
                 If(city_idx == 2, 2,
                    If(city_idx == 3, 5,
                       If(city_idx == 4, 3,
                          If(city_idx == 5, 4,
                             If(city_idx == 6, 4,
                                If(city_idx == 7, 2,
                                   If(city_idx == 8, 2,
                                      If(city_idx == 9, 5, 0)))))))))

# Build allowed_flights set
allowed_flights = set()
flights_list = [
    ("Rome", "Stuttgart"),
    ("Venice", "Rome"),
    ("Dublin", "Bucharest"),
    ("Mykonos", "Rome"),
    ("Seville", "Lisbon"),
    ("Frankfurt", "Venice"),
    ("Venice", "Stuttgart"),
    ("Bucharest", "Lisbon"),
    ("Nice", "Mykonos"),
    ("Venice", "Lisbon"),
    ("Dublin", "Lisbon"),
    ("Venice", "Nice"),
    ("Rome", "Seville"),
    ("Frankfurt", "Rome"),
    ("Nice", "Dublin"),
    ("Rome", "Bucharest"),
    ("Frankfurt", "Dublin"),
    ("Rome", "Dublin"),
    ("Venice", "Dublin"),
    ("Rome", "Lisbon"),
    ("Frankfurt", "Lisbon"),
    ("Nice", "Rome"),
    ("Frankfurt", "Nice"),
    ("Frankfurt", "Stuttgart"),
    ("Frankfurt", "Bucharest"),
    ("Lisbon", "Stuttgart"),
    ("Nice", "Lisbon"),
    ("Seville", "Dublin")
]

for a, b in flights_list:
    allowed_flights.add((city_to_idx[a], city_to_idx[b]))
    allowed_flights.add((city_to_idx[b], city_to_idx[a]))

# Create Z3 solver
solver = Solver()

# Create order variables: order[0] to order[9], each is an integer between 0-9
order = [Int(f'order_{i}') for i in range(10)]

# Add constraints: all order[i] are distinct and between 0-9
solver.add(Distinct(order))
for i in range(10):
    solver.add(And(order[i] >= 0, order[i] <= 9))

# Create start_days and end_days arrays
start_days = [Int(f'start_day_{i}') for i in range(10)]
end_days = [Int(f'end_day_{i}') for i in range(10)]

# Add constraints for start_days and end_days
solver.add(start_days[0] == 1)
solver.add(end_days[0] == start_days[0] + get_duration(order[0]) - 1)

for i in range(1, 10):
    solver.add(start_days[i] == end_days[i-1])
    solver.add(end_days[i] == start_days[i] + get_duration(order[i]) - 1)

# Add constraint that end_day of last city is 23
solver.add(end_days[9] == 23)

# Add constraints for specific cities
# Frankfurt (index 3) must start on day 1
for i in range(10):
    solver.add(If(order[i] == 3, start_days[i] == 1, True))

# Mykonos (index 1) must start on day 10
for i in range(10):
    solver.add(If(order[i] == 1, start_days[i] == 10, True))

# Seville (index 9) must start on day 13
for i in range(10):
    solver.add(If(order[i] == 9, start_days[i] == 13, True))

# Add constraints for allowed transitions between consecutive cities
for i in range(9):
    constraints = []
    for a, b in allowed_flights:
        constraints.append(And(order[i] == a, order[i+1] == b))
    solver.add(Or(constraints))

# Solve
if solver.check() == sat:
    model = solver.model()
    order_values = [model.eval(order[i]).as_long() for i in range(10)]
    start_days_values = [model.eval(start_days[i]).as_long() for i in range(10)]
    end_days_values = [model.eval(end_days[i]).as_long() for i in range(10)]

    # Build itinerary
    itinerary = []
    for i in range(10):
        city_idx = order_values[i]
        city_name = cities[city_idx]
        start = start_days_values[i]
        end = end_days_values[i]
        day_range = f"Day {start}-{end}"
        itinerary.append({"day_range": day_range, "place": city_name})

    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found.")