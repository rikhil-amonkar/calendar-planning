from z3 import *

# Define cities with their durations and fixed dates (if any)
cities = [
    ('Brussels', 2, 1, 2),
    ('Split', 5, None, None),
    ('Barcelona', 7, None, None)
]

# Direct flights between cities (adjacency list)
direct_flights = {
    'Brussels': {'Barcelona'},
    'Barcelona': {'Brussels', 'Split'},
    'Split': {'Barcelona'}
}

solver = Solver()

# Create variables for start and end days for cities without fixed dates
start = {}
end = {}
for city in cities:
    name, duration, fixed_start, fixed_end = city
    if fixed_start is not None:
        start[name] = fixed_start
        end[name] = fixed_end
    else:
        start[name] = Int(f'start_{name}')
        end[name] = Int(f'end_{name}')
        solver.add(end[name] == start[name] + duration - 1)
        solver.add(start[name] >= 1, end[name] <= 12)

# Ensure no overlapping stays
for i in range(len(cities)):
    for j in range(i + 1, len(cities)):
        name_i = cities[i][0]
        name_j = cities[j][0]
        solver.add(Or(end[name_i] < start[name_j], end[name_j] < start[name_i]))

# Define order variables (each position in the itinerary)
order = [Int(f'order_{i}') for i in range(len(cities))]
solver.add(Distinct(order))
for o in order:
    solver.add(o >= 0, o < len(cities))

# Ensure consecutive cities in the itinerary have direct flights
for i in range(len(cities) - 1):
    current = order[i]
    next_city = order[i + 1]
    for idx in range(len(cities)):
        for jdx in range(len(cities)):
            current_name = cities[idx][0]
            next_name = cities[jdx][0]
            solver.add(Implies(And(current == idx, next_city == jdx),
                        next_name in direct_flights.get(current_name, set())))

# Ensure start dates follow the itinerary order
for i in range(len(cities) - 1):
    current = order[i]
    next_city = order[i + 1]
    for idx in range(len(cities)):
        for jdx in range(len(cities)):
            current_name = cities[idx][0]
            next_name = cities[jdx][0]
            solver.add(Implies(And(current == idx, next_city == jdx),
                        start[next_name] == end[current_name] + 1))

if solver.check() == sat:
    model = solver.model()
    order_result = [model.evaluate(o) for o in order]
    schedule = []
    for idx in order_result:
        city = cities[idx.as_long()]
        name = city[0]
        s = model.evaluate(start[name])
        e = model.evaluate(end[name])
        schedule.append((name, s.as_long(), e.as_long()))
    print("Valid itinerary found:")
    for visit in schedule:
        print(f"{visit[0]}: Days {visit[1]} to {visit[2]}")
else:
    print("No valid itinerary possible.")