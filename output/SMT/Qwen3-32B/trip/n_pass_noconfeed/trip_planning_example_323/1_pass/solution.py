from z3 import *
import json

# Define cities as integers: 0=London, 1=Oslo, 2=Split, 3=Porto
cities = [Int(f'city_{i}') for i in range(16)]  # 16 days, 0-based index

solver = Solver()

# Each city must be one of the four
for city in cities:
    solver.add(Or([city == 0, city == 1, city == 2, city == 3]))

# Allowed transitions between cities
allowed_transitions = {(0, 1), (1, 0), (2, 1), (1, 2), (1, 3), (3, 1), (0, 2), (2, 0)}

# Enforce direct flight constraints between consecutive days
for i in range(15):
    prev = cities[i]
    curr = cities[i + 1]
    allowed_pairs = []
    for a, b in allowed_transitions:
        allowed_pairs.append(And(prev == a, curr == b))
    solver.add(Or(prev == curr, Or(allowed_pairs)))

# Split must be visited from day 7 to day 11 (indices 6 to 10)
for i in range(6, 11):
    solver.add(cities[i] == 2)

# Ensure no transitions during days 7-11 (indices 6-10)
for i in range(6, 10):
    solver.add(cities[i] == cities[i + 1])

# Ensure no other days in Split
for i in range(6):  # Days 1-6 (indices 0-5)
    solver.add(cities[i] != 2)
for i in range(11, 16):  # Days 12-16 (indices 11-15)
    solver.add(cities[i] != 2)

# At least one day in London between day 1 and day 7
solver.add(Or([cities[i] == 0 for i in range(7)]))

# Calculate total days for each city considering transitions
def compute_total_contributions(city_id):
    contributions = []
    for i in range(16):
        if i == 0:
            contrib = If(cities[i] == city_id, 1, 0)
        else:
            prev = cities[i - 1]
            curr = cities[i]
            same = prev == curr
            contrib_same = If(curr == city_id, 1, 0)
            contrib_diff_prev = If(prev == city_id, 1, 0)
            contrib_diff_curr = If(curr == city_id, 1, 0)
            contrib = If(same, contrib_same, contrib_diff_prev + contrib_diff_curr)
        contributions.append(contrib)
    return Sum(contributions)

total_London = compute_total_contributions(0)
total_Oslo = compute_total_contributions(1)
total_Porto = compute_total_contributions(3)

# Add constraints for total days in each city
solver.add(total_London == 7)
solver.add(total_Oslo == 2)
solver.add(total_Porto == 5)

# Solve the constraints
if solver.check() == sat:
    model = solver.model()
    # Extract the itinerary
    itinerary_days = []
    for i in range(16):
        day_city = model[cities[i]].as_long()
        itinerary_days.append((i + 1, day_city))  # day numbers are 1-16

    # Group consecutive days
    grouped = []
    current_place = None
    start_day = None
    for day, city in itinerary_days:
        if current_place is None:
            current_place = city
            start_day = day
        elif city == current_place:
            continue
        else:
            grouped.append((start_day, day - 1, current_place))
            current_place = city
            start_day = day
    if current_place is not None:
        grouped.append((start_day, 16, current_place))

    # Map city numbers to names
    city_names = {0: "London", 1: "Oslo", 2: "Split", 3: "Porto"}
    result = []
    for start, end, city_num in grouped:
        result.append({"day_range": f"Day {start}-{end}", "place": city_names[city_num]})

    print(json.dumps({"itinerary": result}))
else:
    print(json.dumps({"error": "No solution found"}))