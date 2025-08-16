from z3 import *
import json

# Define cities
PRAGUE = 0
BERLIN = 1
TALLINN = 2
STOCKHOLM = 3

# Allowed flights
allowed_flights = {
    (PRAGUE, STOCKHOLM), (STOCKHOLM, PRAGUE),
    (PRAGUE, TALLINN), (TALLINN, PRAGUE),
    (BERLIN, TALLINN), (TALLINN, BERLIN),
    (STOCKHOLM, TALLINN), (TALLINN, STOCKHOLM),
    (STOCKHOLM, BERLIN), (BERLIN, STOCKHOLM)
}

# Create solver
s = Solver()

# Create variables for each day's city (days 1 to 12)
city_day = [Int(f'city_day_{d}') for d in range(1, 13)]

# Constraints: each city_day is between 0 and 3
for d in city_day:
    s.add(And(d >= 0, d <= 3))

# Constraints: consecutive days must have allowed flights
for d in range(1, 12):  # days 1 to 11
    prev_city = city_day[d-1]
    curr_city = city_day[d]
    allowed_pairs = []
    for (a, b) in allowed_flights:
        allowed_pairs.append(And(prev_city == a, curr_city == b))
    s.add(Or(*allowed_pairs))

# Calculate total days for each city
total_prague = 0
total_berlin = 0
total_tallinn = 0
total_stockholm = 0

for d in range(1, 13):  # d from 1 to 12
    curr = city_day[d-1]  # city_day is 0-based index for day 1 to 12
    if d == 1:
        total_prague += If(curr == PRAGUE, 1, 0)
        total_berlin += If(curr == BERLIN, 1, 0)
        total_tallinn += If(curr == TALLINN, 1, 0)
        total_stockholm += If(curr == STOCKHOLM, 1, 0)
    else:
        prev = city_day[d-2]
        curr = city_day[d-1]
        same = prev == curr
        contrib_prague = If(same, If(curr == PRAGUE, 1, 0), If(prev == PRAGUE, 1, 0) + If(curr == PRAGUE, 1, 0))
        contrib_berlin = If(same, If(curr == BERLIN, 1, 0), If(prev == BERLIN, 1, 0) + If(curr == BERLIN, 1, 0))
        contrib_tallinn = If(same, If(curr == TALLINN, 1, 0), If(prev == TALLINN, 1, 0) + If(curr == TALLINN, 1, 0))
        contrib_stockholm = If(same, If(curr == STOCKHOLM, 1, 0), If(prev == STOCKHOLM, 1, 0) + If(curr == STOCKHOLM, 1, 0))
        total_prague += contrib_prague
        total_berlin += contrib_berlin
        total_tallinn += contrib_tallinn
        total_stockholm += contrib_stockholm

# Add constraints for total days
s.add(total_prague == 2)
s.add(total_berlin == 3)
s.add(total_tallinn == 5)
s.add(total_stockholm == 5)

# Add constraints for being in Berlin on day 6 and day 8
# Day 6 (index 5 in city_day list)
d = 6
prev = city_day[4]  # day 5
curr = city_day[5]  # day 6
condition = Or(curr == BERLIN, And(prev == BERLIN, curr != prev))
s.add(condition)

# Day 8 (index 7 in city_day list)
d = 8
prev = city_day[6]  # day 7
curr = city_day[7]  # day 8
condition = Or(curr == BERLIN, And(prev == BERLIN, curr != prev))
s.add(condition)

# Add constraint for Tallinn visit between day 8 and 12
s.add(Or(
    city_day[7] == TALLINN,  # day 8
    city_day[8] == TALLINN,  # day 9
    city_day[9] == TALLINN,  # day 10
    city_day[10] == TALLINN,  # day 11
    city_day[11] == TALLINN   # day 12
))

# Now solve
if s.check() == sat:
    m = s.model()
    # Extract the itinerary
    itinerary = []
    for day_index in range(12):
        city = m[city_day[day_index]].as_long()
        city_name = ""
        if city == PRAGUE:
            city_name = "Prague"
        elif city == BERLIN:
            city_name = "Berlin"
        elif city == TALLINN:
            city_name = "Tallinn"
        elif city == STOCKHOLM:
            city_name = "Stockholm"
        itinerary.append({"day": day_index + 1, "city": city_name})
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found.")