from z3 import *
import json

# Define city indices
Prague, Stuttgart, Split, Krakow, Florence = 0, 1, 2, 3, 4
index_to_city = {
    0: 'Prague',
    1: 'Stuttgart',
    2: 'Split',
    3: 'Krakow',
    4: 'Florence'
}
dur = [4, 2, 2, 2, 2]  # Durations for each city

# Define direct flights as unordered pairs
flight_set = set()
flight_set.add((0, 2))  # Prague-Split
flight_set.add((0, 3))  # Prague-Krakow
flight_set.add((0, 4))  # Prague-Florence
flight_set.add((1, 2))  # Stuttgart-Split
flight_set.add((1, 3))  # Stuttgart-Krakow
flight_set.add((2, 3))  # Split-Krakow

s = Solver()

# Order variables for unknown positions
order0 = Int('order0')  # First city
order3 = Int('order3')  # Fourth city
order4 = Int('order4')  # Fifth city

# Order list (second and third are fixed as Stuttgart and Split)
order = [order0, Stuttgart, Split, order3, order4]

# Constraints: all cities in order must be distinct
s.add(Distinct(order))

# First city must be Krakow or Florence (both have 2-day duration)
s.add(Or(order0 == 3, order0 == 4))

# Helper function to check flight connectivity
def are_connected(a, b):
    conditions = []
    for (i, j) in flight_set:
        conditions.append(And(a == i, b == j))
        conditions.append(And(a == j, b == i))
    return Or(conditions)

# Flight constraints between consecutive cities
s.add(are_connected(order0, Stuttgart))  # First to second
s.add(are_connected(Split, order3))      # Third to fourth
s.add(are_connected(order3, order4))     # Fourth to fifth

# One of the last two cities must be Prague (to satisfy duration sum)
s.add(Or(order3 == 0, order4 == 0))

if s.check() == sat:
    m = s.model()
    order0_val = m[order0].as_long()
    order3_val = m[order3].as_long()
    order4_val = m[order4].as_long()
    order_vals = [order0_val, Stuttgart, Split, order3_val, order4_val]
    
    # Compute start and end days for each city
    start_vals = [0] * 5
    end_vals = [0] * 5
    
    # Fixed stays for Stuttgart and Split
    start_vals[Stuttgart] = 2
    end_vals[Stuttgart] = 3
    start_vals[Split] = 3
    end_vals[Split] = 4
    
    # First city
    start_vals[order0_val] = 1
    end_vals[order0_val] = 2
    
    # Fourth city
    start_vals[order3_val] = 4
    end_vals[order3_val] = start_vals[order3_val] + dur[order3_val] - 1
    
    # Fifth city
    start_vals[order4_val] = end_vals[order3_val]
    end_vals[order4_val] = 8
    
    # Build itinerary
    itinerary = []
    for i, city_idx in enumerate(order_vals):
        city_name = index_to_city[city_idx]
        s_val = start_vals[city_idx]
        e_val = end_vals[city_idx]
        itinerary.append({"day_range": f"Day {s_val}-{e_val}", "place": city_name})
        
        if i < 4:  # Not the last city
            next_city_idx = order_vals[i+1]
            next_city_name = index_to_city[next_city_idx]
            flight_day = e_val
            itinerary.append({"day_range": f"Day {flight_day}", "place": city_name})
            itinerary.append({"day_range": f"Day {flight_day}", "place": next_city_name})
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))
else:
    print(json.dumps({"itinerary": []}))