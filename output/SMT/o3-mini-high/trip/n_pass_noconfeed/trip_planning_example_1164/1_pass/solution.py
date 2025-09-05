import json
from z3 import Solver, Int, Distinct, If, And, Or, sat

# Define city indices and their attributes
# City IDs: 0: Reykjavik, 1: Stockholm, 2: Porto, 3: Nice, 4: Venice, 5: Vienna, 6: Split, 7: Copenhagen
city_names = {
    0: "Reykjavik",
    1: "Stockholm",
    2: "Porto",
    3: "Nice",
    4: "Venice",
    5: "Vienna",
    6: "Split",
    7: "Copenhagen"
}
# Durations for each city (in days)
durations_data = {
    0: 2,
    1: 2,
    2: 5,
    3: 3,
    4: 4,
    5: 3,
    6: 3,
    7: 2
}

# Define allowed direct flight connections (undirected pairs)
allowed_pairs = [
    (7, 5),   # Copenhagen - Vienna
    (3, 1),   # Nice - Stockholm
    (6, 7),   # Split - Copenhagen
    (3, 0),   # Nice - Reykjavik
    (3, 2),   # Nice - Porto
    (0, 5),   # Reykjavik - Vienna
    (1, 7),   # Stockholm - Copenhagen
    (3, 4),   # Nice - Venice
    (3, 5),   # Nice - Vienna
    (0, 7),   # Reykjavik - Copenhagen
    (3, 7),   # Nice - Copenhagen
    (1, 5),   # Stockholm - Vienna
    (4, 5),   # Venice - Vienna
    (7, 2),   # Copenhagen - Porto
    (0, 1),   # Reykjavik - Stockholm
    (1, 6),   # Stockholm - Split
    (6, 5),   # Split - Vienna
    (7, 4),   # Copenhagen - Venice
    (5, 2)    # Vienna - Porto
]

# SMT model
s = Solver()

# Create itinerary variables: an ordering of 8 cities (each city appears once)
n = 8
itinerary = [Int(f"city_{i}") for i in range(n)]
for city in itinerary:
    s.add(city >= 0, city < n)
s.add(Distinct(*itinerary))

# Create time variables for each visit segment
starts = [Int(f"start_{i}") for i in range(n)]
ends = [Int(f"end_{i}") for i in range(n)]
for i in range(n):
    s.add(starts[i] >= 1, starts[i] <= 17)
    s.add(ends[i] >= 1, ends[i] <= 17)

# Fix the itinerary total: starting on day 1 and ending on day 17
s.add(starts[0] == 1)
s.add(ends[n - 1] == 17)

# Function to get duration using if-then-else for the city in a given segment
def get_duration(city_var):
    return If(city_var == 0, durations_data[0],
           If(city_var == 1, durations_data[1],
           If(city_var == 2, durations_data[2],
           If(city_var == 3, durations_data[3],
           If(city_var == 4, durations_data[4],
           If(city_var == 5, durations_data[5],
           If(city_var == 6, durations_data[6],
           If(city_var == 7, durations_data[7], 0))))))))

durations_vars = [get_duration(itinerary[i]) for i in range(n)]

# Each visit segment: end = start + duration - 1 (because the day traveling counts for both origin and destination)
for i in range(n):
    s.add(ends[i] == starts[i] + durations_vars[i] - 1)

# Transitions: when flying from a segment to the next, the flight day counts for both.
for i in range(n - 1):
    s.add(starts[i + 1] == ends[i])

# Flight connectivity constraints: consecutive cities must have a direct flight connection.
for i in range(n - 1):
    a = itinerary[i]
    b = itinerary[i + 1]
    allowed_exprs = []
    for (x, y) in allowed_pairs:
        allowed_exprs.append(Or(And(a == x, b == y), And(a == y, b == x)))
    s.add(Or(*allowed_exprs))

# Special meeting/workshop/wedding constraints:
# Reykjavik (ID 0): Stay 2 days and meet a friend between day 3 and day 4.
for i in range(n):
    s.add(Or(itinerary[i] != 0,
             Or(And(starts[i] <= 3, 3 <= ends[i]),
                And(starts[i] <= 4, 4 <= ends[i]))))
# Stockholm (ID 1): Stay 2 days and meet friends between day 4 and day 5.
for i in range(n):
    s.add(Or(itinerary[i] != 1,
             Or(And(starts[i] <= 4, 4 <= ends[i]),
                And(starts[i] <= 5, 5 <= ends[i]))))
# Porto (ID 2): Stay 5 days and attend a wedding between day 13 and day 17.
for i in range(n):
    s.add(Or(itinerary[i] != 2,
             Or(And(starts[i] <= 13, 13 <= ends[i]),
                And(starts[i] <= 14, 14 <= ends[i]),
                And(starts[i] <= 15, 15 <= ends[i]),
                And(starts[i] <= 16, 16 <= ends[i]),
                And(starts[i] <= 17, 17 <= ends[i]))))
# Vienna (ID 5): Stay 3 days and attend a workshop between day 11 and day 13.
for i in range(n):
    s.add(Or(itinerary[i] != 5,
             Or(And(starts[i] <= 11, 11 <= ends[i]),
                And(starts[i] <= 12, 12 <= ends[i]),
                And(starts[i] <= 13, 13 <= ends[i]))))

# Solve the SMT constraints
if s.check() == sat:
    m = s.model()
    itinerary_plan = []
    for i in range(n):
        start_day = m.evaluate(starts[i]).as_long()
        end_day = m.evaluate(ends[i]).as_long()
        city_val = m.evaluate(itinerary[i]).as_long()
        itinerary_plan.append({
            "day_range": f"Day {start_day}-{end_day}",
            "place": city_names[city_val]
        })
    result = {"itinerary": itinerary_plan}
    print(json.dumps(result))
else:
    print(json.dumps({"itinerary": []}))