import json
from z3 import *

def Duration(city):
    # Returns the required duration (in days) for the given city (represented as a Z3 Int)
    return If(city == 0, 2,
           If(city == 1, 5,
           If(city == 2, 4,
           If(city == 3, 2,
           If(city == 4, 4,
           If(city == 5, 4,
           If(city == 6, 3,
           If(city == 7, 5,
           If(city == 8, 4, 0)))))))))

# Mapping of city indices to names:
city_names = {
    0: "Salzburg",
    1: "Venice",
    2: "Bucharest",
    3: "Brussels",
    4: "Hamburg",
    5: "Copenhagen",
    6: "Nice",
    7: "Zurich",
    8: "Naples"
}

# Allowed direct flights (treat flights as bidirectional)
allowed_flights = set()
def add_flight(a, b):
    # store flights as sorted tuples
    allowed_flights.add(tuple(sorted((a, b))))

# Define the allowed direct flights using city indices:
add_flight(7, 3)   # Zurich - Brussels
add_flight(2, 5)   # Bucharest - Copenhagen
add_flight(1, 3)   # Venice - Brussels
add_flight(6, 7)   # Nice - Zurich
add_flight(4, 6)   # Hamburg - Nice
add_flight(7, 8)   # Zurich - Naples
add_flight(4, 2)   # Hamburg - Bucharest
add_flight(7, 5)   # Zurich - Copenhagen
add_flight(2, 3)   # Bucharest - Brussels
add_flight(3, 4)   # Brussels - Hamburg
add_flight(1, 8)   # Venice - Naples
add_flight(1, 5)   # Venice - Copenhagen
add_flight(2, 8)   # Bucharest - Naples
add_flight(4, 5)   # Hamburg - Copenhagen
add_flight(1, 7)   # Venice - Zurich
add_flight(3, 6)   # Brussels - Nice
add_flight(1, 4)   # Venice - Hamburg
add_flight(5, 8)   # Copenhagen - Naples
add_flight(6, 8)   # Nice - Naples
add_flight(4, 7)   # Hamburg - Zurich
add_flight(0, 4)   # Salzburg - Hamburg
add_flight(2, 7)   # Bucharest - Zurich
add_flight(3, 8)   # Brussels - Naples
add_flight(3, 5)   # Brussels - Copenhagen
add_flight(1, 6)   # Venice - Nice
add_flight(5, 6)   # Copenhagen - Nice

# Create the Z3 solver instance
solver = Solver()

# The itinerary order: a list of 9 integer variables representing city indices (0 ... 8)
order = [Int(f"order_{i}") for i in range(9)]
for i in range(9):
    solver.add(And(order[i] >= 0, order[i] <= 8))
solver.add(Distinct(order))

# Start times for each city's stay block (day numbers, from 1 to 25)
start_times = [Int(f"s_{i}") for i in range(9)]
# The trip starts on day 1.
solver.add(start_times[0] == 1)

# Add constraints linking consecutive city blocks.
# If you depart from city A on a flight on day X, you also arrive in city B on day X.
for i in range(1, 9):
    # s[i] = s[i-1] + Duration(city at position i-1) - 1
    solver.add(start_times[i] == start_times[i-1] + Duration(order[i-1]) - 1)

# Final condition: the last city's stay must end on day 25.
solver.add(start_times[8] + Duration(order[8]) - 1 == 25)

# Flight constraint: consecutive cities must be connected by a direct flight.
for i in range(8):
    valid_flights = []
    for (a, b) in allowed_flights:
        # Allowed if (order[i] is a and order[i+1] is b) or vice versa.
        valid_flights.append(Or(And(order[i] == a, order[i+1] == b),
                                 And(order[i] == b, order[i+1] == a)))
    solver.add(Or(valid_flights))

# Event constraints:
# If a city with a special event is visited at a certain block, its stay must overlap the event's days.
# Note: a city's interval is [s, s + Duration(city) - 1]

# Brussels (city index 3): meet friends between day 21 and 22.
for i in range(9):
    solver.add(If(order[i] == 3,
                  And(start_times[i] <= 22, start_times[i] + 2 - 1 >= 21),
                  True))
# Copenhagen (city index 5): wedding between day 18 and 21.
for i in range(9):
    solver.add(If(order[i] == 5,
                  And(start_times[i] <= 21, start_times[i] + 4 - 1 >= 18),
                  True))
# Nice (city index 6): visit relatives between day 9 and 11.
for i in range(9):
    solver.add(If(order[i] == 6,
                  And(start_times[i] <= 11, start_times[i] + 3 - 1 >= 9),
                  True))
# Naples (city index 8): workshop between day 22 and 25.
for i in range(9):
    solver.add(If(order[i] == 8,
                  And(start_times[i] <= 25, start_times[i] + 4 - 1 >= 22),
                  True))

# Solve the constraints
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    # A lookup for fixed durations
    fixed_durations = {0: 2, 1: 5, 2: 4, 3: 2, 4: 4, 5: 4, 6: 3, 7: 5, 8: 4}
    for i in range(9):
        city_idx = model.evaluate(order[i]).as_long()
        city_name = city_names[city_idx]
        start_day = model.evaluate(start_times[i]).as_long()
        dur = fixed_durations[city_idx]
        end_day = start_day + dur - 1
        itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": city_name})
    output = {"itinerary": itinerary}
    print(json.dumps(output))
else:
    # No valid itinerary found.
    print(json.dumps({"itinerary": []}))