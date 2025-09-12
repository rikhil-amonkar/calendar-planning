from z3 import *
import json

# Define cities and direct flights
cities = ["Copenhagen", "Geneva", "Mykonos", "Naples", "Prague", "Dubrovnik", "Athens", "Santorini", "Brussels", "Munich"]

direct_flights = {
    ("Copenhagen", "Dubrovnik"), ("Dubrovnik", "Copenhagen"),
    ("Brussels", "Copenhagen"), ("Copenhagen", "Brussels"),
    ("Prague", "Geneva"), ("Geneva", "Prague"),
    ("Athens", "Geneva"), ("Geneva", "Athens"),
    ("Naples", "Dubrovnik"), ("Dubrovnik", "Naples"),
    ("Athens", "Dubrovnik"), ("Dubrovnik", "Athens"),
    ("Geneva", "Mykonos"), ("Mykonos", "Geneva"),
    ("Naples", "Mykonos"), ("Mykonos", "Naples"),
    ("Naples", "Copenhagen"), ("Copenhagen", "Naples"),
    ("Munich", "Mykonos"), ("Mykonos", "Munich"),
    ("Naples", "Athens"), ("Athens", "Naples"),
    ("Prague", "Athens"), ("Athens", "Prague"),
    ("Santorini", "Geneva"), ("Geneva", "Santorini"),
    ("Athens", "Santorini"), ("Santorini", "Athens"),
    ("Naples", "Munich"), ("Munich", "Naples"),
    ("Prague", "Copenhagen"), ("Copenhagen", "Prague"),
    ("Brussels", "Naples"), ("Naples", "Brussels"),
    ("Athens", "Copenhagen"), ("Copenhagen", "Athens"),
    ("Naples", "Geneva"), ("Geneva", "Naples"),
    ("Dubrovnik", "Munich"), ("Munich", "Dubrovnik"),
    ("Brussels", "Munich"), ("Munich", "Brussels"),
    ("Prague", "Brussels"), ("Brussels", "Prague"),
    ("Brussels", "Athens"), ("Athens", "Brussels"),
    ("Athens", "Munich"), ("Munich", "Athens"),
    ("Geneva", "Munich"), ("Munich", "Geneva"),
    ("Copenhagen", "Munich"), ("Munich", "Copenhagen"),
    ("Brussels", "Geneva"), ("Geneva", "Brussels"),
    ("Copenhagen", "Geneva"), ("Geneva", "Copenhagen"),
    ("Prague", "Munich"), ("Munich", "Prague"),
    ("Copenhagen", "Santorini"), ("Santorini", "Copenhagen"),
    ("Naples", "Santorini"), ("Santorini", "Naples"),
    ("Geneva", "Dubrovnik"), ("Dubrovnik", "Geneva")
}

# Create Z3 solver
s = Solver()

# Create EnumSort for cities
city_sort, city_consts = EnumSort('City', cities)

# Map city names to Z3 constants
city_consts_dict = {city: const for city, const in zip(cities, city_consts)}

# Create sequence of 10 cities (Z3 expressions)
sequence = [Const(f'pos_{i}', city_sort) for i in range(10)]

# Ensure all cities are distinct
s.add(Distinct(sequence))

# Define duration variables and start_day variables
d = [Int(f'd_{i}') for i in range(10)]
start_day = [Int(f's_{i}') for i in range(10)]

# Constraints for d_i >= 0
for di in d:
    s.add(di >= 0)

# Sum of d_i = 19
s.add(Sum(d) == 19)

# Constraints for start_day
for i in range(10):
    if i == 0:
        s.add(start_day[i] == 1)
    else:
        prev_pos = i - 1
        duration_prev = If(Or(prev_pos == 0, prev_pos == 9), d[prev_pos] + 1, d[prev_pos] + 2)
        end_prev = start_day[prev_pos] + duration_prev - 1
        s.add(start_day[i] == end_prev + 1)

# Required durations
required_duration = {
    "Copenhagen": 5,
    "Geneva": 3,
    "Mykonos": 2,
    "Naples": 4,
    "Prague": 2,
    "Dubrovnik": 3,
    "Athens": 4,
    "Santorini": 5,
    "Brussels": 4,
    "Munich": 5
}

# Add duration constraints for each city in sequence
for i in range(10):
    for c in cities:
        is_city = sequence[i] == city_consts_dict[c]
        required = required_duration[c]
        is_first_or_last = Or(i == 0, i == 9)
        duration_expr = If(is_first_or_last, d[i] + 1, d[i] + 2)
        s.add(If(is_city, duration_expr == required, True))

# Add flight constraints between consecutive cities
for i in range(9):
    a, b = sequence[i], sequence[i + 1]
    valid_pairs = [And(a == city_consts_dict[x], b == city_consts_dict[y]) for x, y in direct_flights]
    s.add(Or(valid_pairs))

# Add specific event constraints
# Mykonos in last position
s.add(sequence[9] == city_consts_dict["Mykonos"])
s.add(start_day[9] == 27)
s.add(d[9] == 1)

# Workshop in Athens between day 8 and 11
for i in range(10):
    c = sequence[i]
    is_athens = c == city_consts_dict["Athens"]
    duration_expr = If(Or(i == 0, i == 9), d[i] + 1, d[i] + 2)
    end_day_expr = start_day[i] + duration_expr - 1
    s.add(If(is_athens, And(start_day[i] <= 11, end_day_expr >= 8), True))

# Relatives in Naples between day 5 and 8
for i in range(10):
    c = sequence[i]
    is_naples = c == city_consts_dict["Naples"]
    duration_expr = If(Or(i == 0, i == 9), d[i] + 1, d[i] + 2)
    end_day_expr = start_day[i] + duration_expr - 1
    s.add(If(is_naples, And(start_day[i] <= 8, end_day_expr >= 5), True))

# Friend in Copenhagen between day 11 and 15
for i in range(10):
    c = sequence[i]
    is_cph = c == city_consts_dict["Copenhagen"]
    duration_expr = If(Or(i == 0, i == 9), d[i] + 1, d[i] + 2)
    end_day_expr = start_day[i] + duration_expr - 1
    s.add(If(is_cph, And(start_day[i] <= 15, end_day_expr >= 11), True))

# Solve the constraints
if s.check() == sat:
    m = s.model()
    seq = [m.evaluate(seq_i).as_string() for seq_i in sequence]
    durations = [m.evaluate(d_i).as_long() for d_i in d]
    start_days = [m.evaluate(sdi).as_long() for sdi in start_day]

    itinerary = []
    for i in range(10):
        city = seq[i]
        duration = durations[i]
        if i == 0 or i == 9:
            city_duration = duration + 1
        else:
            city_duration = duration + 2
        end_day = start_days[i] + city_duration - 1
        day_range = f"Day {start_days[i]}-{end_day}"
        itinerary.append({"day_range": day_range, "place": city})

    print(json.dumps({"itinerary": itinerary}))
else:
    print("No solution found.")