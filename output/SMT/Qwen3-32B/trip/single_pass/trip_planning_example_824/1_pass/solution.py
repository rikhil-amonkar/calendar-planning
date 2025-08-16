from z3 import *
import json

# Define the cities
cities = ["Berlin", "Split", "Bucharest", "Riga", "Lisbon", "Tallinn", "Lyon"]
direct_flights = {
    ("Lisbon", "Bucharest"),
    ("Berlin", "Lisbon"),
    ("Bucharest", "Riga"),
    ("Berlin", "Riga"),
    ("Split", "Lyon"),
    ("Lisbon", "Riga"),
    ("Riga", "Tallinn"),
    ("Berlin", "Split"),
    ("Lyon", "Lisbon"),
    ("Berlin", "Tallinn"),
    ("Lyon", "Bucharest"),
}

# Required durations for each city
required_durations = {
    "Berlin": 5,
    "Split": 3,
    "Bucharest": 3,
    "Riga": 5,
    "Lisbon": 3,
    "Tallinn": 4,
    "Lyon": 5,
}

# Z3 solver setup
s = Solver()

# Variables
# The order of cities (permutation of the 7 cities, first is Berlin)
order = [Int(f"order_{i}") for i in range(7)]
# Map each city to its index in the order
city_to_index = {city: i for i, city in enumerate(cities)}
# Constraints to ensure it's a permutation
s.add(Distinct(order))
s.add(And([0 <= order[i], order[i] < 7 for i in range(7)]))
# First city must be Berlin
s.add(order[0] == city_to_index["Berlin"])

# Start and end days for each city in the order
start_day = [Int(f"start_day_{i}") for i in range(7)]
end_day = [Int(f"end_day_{i}") for i in range(7)]

# Constraints for start and end days
for i in range(7):
    city = cities[order[i]]
    s.add(start_day[i] == If(i == 0, 1, end_day[i-1] + 1))
    s.add(end_day[i] == start_day[i] + required_durations[city] - 1)

# Constraint for total end day to be 22
s.add(end_day[6] == 22)

# Constraint for Lyon's stay to include days 7-11
lyon_index = [i for i in range(7) if cities[order[i]] == "Lyon"][0]
s.add(And(start_day[lyon_index] <= 7, end_day[lyon_index] >= 11))

# Constraint for Bucharest's stay to include at least one day between 13-15
bucharest_index = [i for i in range(7) if cities[order[i]] == "Bucharest"][0]
s.add(And(start_day[bucharest_index] <= 15, end_day[bucharest_index] >= 13))
s.add(start_day[bucharest_index] >= 11)
s.add(start_day[bucharest_index] <= 13)

# Constraints for direct flights between consecutive cities
for i in range(6):
    prev_city = cities[order[i]]
    next_city = cities[order[i+1]]
    s.add(Or((prev_city, next_city) in direct_flights, (next_city, prev_city) in direct_flights))

# Solve
if s.check() == sat:
    m = s.model()
    # Extract the order
    order_vals = [m.eval(order[i]).as_long() for i in range(7)]
    actual_order = [cities[order_vals[i]] for i in range(7)]
    
    # Extract start and end days
    start_days = [m.eval(start_day[i]).as_long() for i in range(7)]
    end_days = [m.eval(end_day[i]).as_long() for i in range(7)]
    
    # Build the itinerary
    itinerary = {}
    current_day = 1
    for i in range(7):
        city = actual_order[i]
        sd = start_days[i]
        ed = end_days[i]
        for day in range(sd, ed + 1):
            itinerary[day] = city
    
    # Output the JSON
    print(json.dumps({"itinerary": [{"day": day, "city": city} for day, city in sorted(itinerary.items())]}))
else:
    print("No solution found.")