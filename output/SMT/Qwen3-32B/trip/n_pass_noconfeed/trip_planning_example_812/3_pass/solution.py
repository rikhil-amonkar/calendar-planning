from z3 import Solver, Int, Array, K, sat, Distinct, ForAll, And, Or, If, Not, Select, Store
import json

# Define cities and their visit durations
cities = ["Paris", "Rome", "London", "Berlin", "Madrid", "Vienna", "Prague"]
durations_str = {
    "Paris": 3,
    "Rome": 2,
    "London": 4,
    "Berlin": 3,
    "Madrid": 2,
    "Vienna": 1,
    "Prague": 2
}

# Create Z3 solver
s = Solver()

# Define index range (for 7 cities)
index = Int('index')
i = Int('i')

# Create variables
order = Array('order', IntSort(), IntSort())  # order[i] = city index at position i
start_days = [Int(f'start_day_{i}') for i in range(7)]

# Map city names to indices
city_to_index = {city: idx for idx, city in enumerate(cities)}
index_to_city = {idx: city for idx, city in enumerate(cities)}

# Constraints
# 1. order must be a permutation of 0 to 6 (i.e., all distinct)
s.add(Distinct([order[i] for i in range(7)]))
s.add(And([0 <= order[i], order[i] < 7 for i in range(7)]))

# 2. Start days must be non-negative and increasing
s.add(And([start_days[i] >= 0 for i in range(7)]))
for i in range(6):
    s.add(start_days[i + 1] >= start_days[i] + durations_str[index_to_city[order[i]]])

# 3. No overlapping stays
for i in range(7):
    duration_i = durations_str[index_to_city[order[i]]]
    for j in range(i + 1, 7):
        duration_j = durations_str[index_to_city[order[j]]]
        s.add(Or(
            start_days[j] >= start_days[i] + duration_i,
            start_days[i] >= start_days[j] + duration_j
        ))

# Check for solution
if s.check() == sat:
    model = s.model()

    # Extract the order as city names
    order_result = [index_to_city[model[order[i]].as_long()] for i in range(7)]

    # Compute start and end days for each city
    itinerary = []
    for i in range(7):
        city_name = order_result[i]
        start_day = model[start_days[i]].as_long()
        end_day = start_day + durations_str[city_name] - 1
        itinerary.append({
            "day_range": f"Day {start_day}-{end_day}",
            "place": city_name
        })

    # Output as JSON
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found.")