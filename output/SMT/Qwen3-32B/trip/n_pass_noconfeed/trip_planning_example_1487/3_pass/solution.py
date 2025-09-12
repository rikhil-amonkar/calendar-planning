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

# Define required duration for each city (sum to 21 days)
required_duration = {
    "Copenhagen": 2,
    "Geneva": 3,
    "Mykonos": 1,
    "Naples": 2,
    "Prague": 1,
    "Dubrovnik": 1,
    "Athens": 3,
    "Santorini": 2,
    "Brussels": 2,
    "Munich": 4
}

# Function to get required duration for a city
def get_required_duration(city):
    return If(
        city == city_consts_dict["Copenhagen"], 2,
        If(city == city_consts_dict["Geneva"], 3,
           If(city == city_consts_dict["Mykonos"], 1,
              If(city == city_consts_dict["Naples"], 2,
                 If(city == city_consts_dict["Prague"], 1,
                    If(city == city_consts_dict["Dubrovnik"], 1,
                       If(city == city_consts_dict["Athens"], 3,
                          If(city == city_consts_dict["Santorini"], 2,
                             If(city == city_consts_dict["Brussels"], 2, 4)))))))

# Create start_day variables
start_day = [Int(f's_{i}') for i in range(10)]

# Add start_day constraints
s.add(start_day[0] == 1)
for i in range(1, 10):
    prev_city = sequence[i-1]
    prev_stay = get_required_duration(prev_city)
    s.add(start_day[i] == start_day[i-1] + prev_stay + 1)

# Ensure the last day is 30
last_city = sequence[9]
last_stay = get_required_duration(last_city)
s.add(start_day[9] + last_stay - 1 == 30)

# Add flight constraints between consecutive cities
for i in range(9):
    a, b = sequence[i], sequence[i + 1]
    valid_pairs = [And(a == city_consts_dict[x], b == city_consts_dict[y]) for x, y in direct_flights]
    s.add(Or(valid_pairs))

# Add specific event constraints
# Mykonos in last position
s.add(sequence[9] == city_consts_dict["Mykonos"])

# Workshop in Athens between day 8 and 11
for i in range(10):
    is_athens = sequence[i] == city_consts_dict["Athens"]
    start = start_day[i]
    end = start + get_required_duration(sequence[i]) - 1
    s.add(If(is_athens, And(start <= 11, end >= 8), True))

# Relatives in Naples between day 5 and 8
for i in range(10):
    is_naples = sequence[i] == city_consts_dict["Naples"]
    start = start_day[i]
    end = start + get_required_duration(sequence[i]) - 1
    s.add(If(is_naples, And(start <= 8, end >= 5), True))

# Friend in Copenhagen between day 11 and 15
for i in range(10):
    is_cph = sequence[i] == city_consts_dict["Copenhagen"]
    start = start_day[i]
    end = start + get_required_duration(sequence[i]) - 1
    s.add(If(is_cph, And(start <= 15, end >= 11), True))

# Solve the constraints
if s.check() == sat:
    m = s.model()
    seq = [m.evaluate(seq_i).as_string() for seq_i in sequence]
    start_days = [m.evaluate(sdi).as_long() for sdi in start_day]

    itinerary = []
    for i in range(10):
        city = seq[i]
        stay = get_required_duration(city_consts_dict[city])
        end_day = start_days[i] + stay - 1
        day_range = f"Day {start_days[i]}-{end_day}"
        itinerary.append({"day_range": day_range, "place": city})

    print(json.dumps({"itinerary": itinerary}))
else:
    print("No solution found.")