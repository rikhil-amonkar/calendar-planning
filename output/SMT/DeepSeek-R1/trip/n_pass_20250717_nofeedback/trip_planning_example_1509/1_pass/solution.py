import json
from z3 import *

# Define city names and their indices
city_names = ["Paris", "Warsaw", "Krakow", "Tallinn", "Riga", "Copenhagen", "Helsinki", "Oslo", "Santorini", "Lyon"]
city_index = {name: idx for idx, name in enumerate(city_names)}
durations_arr = [5, 2, 2, 2, 2, 5, 5, 5, 2, 4]  # Corresponding to city_names order

# Define direct flight edges as tuples of city indices
edges = [
    (city_index["Warsaw"], city_index["Riga"]),
    (city_index["Warsaw"], city_index["Tallinn"]),
    (city_index["Copenhagen"], city_index["Helsinki"]),
    (city_index["Lyon"], city_index["Paris"]),
    (city_index["Copenhagen"], city_index["Warsaw"]),
    (city_index["Lyon"], city_index["Oslo"]),
    (city_index["Paris"], city_index["Oslo"]),
    (city_index["Paris"], city_index["Riga"]),
    (city_index["Krakow"], city_index["Helsinki"]),
    (city_index["Paris"], city_index["Tallinn"]),
    (city_index["Oslo"], city_index["Riga"]),
    (city_index["Krakow"], city_index["Warsaw"]),
    (city_index["Paris"], city_index["Helsinki"]),
    (city_index["Copenhagen"], city_index["Santorini"]),
    (city_index["Helsinki"], city_index["Warsaw"]),
    (city_index["Helsinki"], city_index["Riga"]),
    (city_index["Copenhagen"], city_index["Krakow"]),
    (city_index["Copenhagen"], city_index["Riga"]),
    (city_index["Paris"], city_index["Krakow"]),
    (city_index["Copenhagen"], city_index["Oslo"]),
    (city_index["Oslo"], city_index["Tallinn"]),
    (city_index["Oslo"], city_index["Helsinki"]),
    (city_index["Copenhagen"], city_index["Tallinn"]),
    (city_index["Oslo"], city_index["Krakow"]),
    (city_index["Riga"], city_index["Tallinn"]),
    (city_index["Helsinki"], city_index["Tallinn"]),
    (city_index["Paris"], city_index["Copenhagen"]),
    (city_index["Paris"], city_index["Warsaw"]),
    (city_index["Santorini"], city_index["Oslo"]),
    (city_index["Oslo"], city_index["Warsaw"])
]

# Event cities with their indices, durations, and day range constraints
event_cities = [
    ("Paris", city_index["Paris"], 5, (4, 8)),
    ("Krakow", city_index["Krakow"], 2, (17, 18)),
    ("Riga", city_index["Riga"], 2, (23, 24)),
    ("Santorini", city_index["Santorini"], 2, (12, 13)),
    ("Helsinki", city_index["Helsinki"], 5, (18, 22))
]

# Initialize Z3 solver
s = Solver()

# Define order variables: order[i] is the city index at position i
order = [Int('order_%d' % i) for i in range(10)]
for i in range(10):
    s.add(order[i] >= 0, order[i] < 10)
s.add(Distinct(order))

# Define duration for each position
d_arr = []
for i in range(10):
    d_i = If(
        order[i] == 0, 5,
        If(order[i] == 1, 2,
        If(order[i] == 2, 2,
        If(order[i] == 3, 2,
        If(order[i] == 4, 2,
        If(order[i] == 5, 5,
        If(order[i] == 6, 5,
        If(order[i] == 7, 5,
        If(order[i] == 8, 2,
        4))))))))
    d_arr.append(d_i)

# Flight constraints for consecutive cities
for i in range(9):
    edge_cond = Or([Or(And(order[i] == u, order[i+1] == v), And(order[i] == v, order[i+1] == u)) for (u, v) in edges])
    s.add(edge_cond)

# Event constraints
for (name, c_index, dur, (low, high)) in event_cities:
    k_city = Int('k_' + name)
    s.add(And([(order[i] == c_index) == (k_city == i) for i in range(10)]))
    total_before = 0
    for i in range(10):
        total_before = total_before + If(i < k_city, d_arr[i], 0)
    start_day = 1 + total_before - k_city
    end_day = start_day + dur - 1
    s.add(start_day <= high)
    s.add(end_day >= low)

# Solve the problem
if s.check() == sat:
    m = s.model()
    order_val = [m.evaluate(order[i]).as_long() for i in range(10)]
    
    # Map city index to its position in the sequence
    city_position = [0] * 10
    for pos, c_idx in enumerate(order_val):
        city_position[c_idx] = pos
    
    # Calculate start and end days for each city
    starts = [0] * 10
    ends = [0] * 10
    cum_sum = 0
    for pos in range(10):
        c_idx = order_val[pos]
        d_val = durations_arr[c_idx]
        if pos == 0:
            start_day_val = 1
        else:
            start_day_val = cum_sum - pos + 1
        end_day_val = start_day_val + d_val - 1
        starts[c_idx] = start_day_val
        ends[c_idx] = end_day_val
        cum_sum += d_val
    
    # Generate itinerary
    itinerary = []
    for day in range(1, 26):
        cities_today = []
        for c_idx in range(10):
            if starts[c_idx] <= day <= ends[c_idx]:
                cities_today.append(c_idx)
        cities_today.sort(key=lambda idx: city_position[idx])
        if len(cities_today) == 1:
            itinerary.append(city_names[cities_today[0]])
        else:
            itinerary.append(f"{city_names[cities_today[0]]} and {city_names[cities_today[1]]}")
    
    # Output as JSON
    result = {'itinerary': itinerary}
    print(json.dumps(result))
else:
    print("No solution found")