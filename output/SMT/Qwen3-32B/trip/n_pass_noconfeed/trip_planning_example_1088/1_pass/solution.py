from z3 import *
import json

# Define cities
Cities, (Reykjavik, Stuttgart, Oslo, Split, Geneva, Porto, Tallinn, Stockholm) = EnumSort('Cities', ['Reykjavik', 'Stuttgart', 'Oslo', 'Split', 'Geneva', 'Porto', 'Tallinn', 'Stockholm'])

solver = Solver()

# Define cities_order as a list of 8 cities
cities_order = [Const(f'city_{i}', Cities) for i in range(8)]

# All cities are distinct
solver.add(Distinct(cities_order))

# First city is Reykjavik, last is Porto
solver.add(cities_order[0] == Reykjavik)
solver.add(cities_order[7] == Porto)

# Define start_day and end_day for each city in the sequence
start_day = [Int(f'start_day_{i}') for i in range(8)]
end_day = [Int(f'end_day_{i}') for i in range(8)]

# First start_day is 1
solver.add(start_day[0] == 1)

# Consecutive start_day and end_day
for i in range(7):
    solver.add(start_day[i+1] == end_day[i])

# Define duration for each city
for i in range(8):
    duration_expr = If(cities_order[i] == Reykjavik, 2,
        If(cities_order[i] == Stuttgart, 5,
        If(cities_order[i] == Oslo, 5,
        If(cities_order[i] == Split, 3,
        If(cities_order[i] == Geneva, 2,
        If(cities_order[i] == Porto, 3,
        If(cities_order[i] == Tallinn, 5,
        If(cities_order[i] == Stockholm, 3, 0)))))))
    )
    solver.add(end_day[i] == start_day[i] + duration_expr - 1)

# Last city ends on day 21
solver.add(end_day[7] == 21)

# Allowed direct flights
allowed_pairs = [
    (Reykjavik, Stuttgart), (Stuttgart, Reykjavik),
    (Reykjavik, Stockholm), (Stockholm, Reykjavik),
    (Reykjavik, Tallinn), (Tallinn, Reykjavik),
    (Stockholm, Oslo), (Oslo, Stockholm),
    (Stuttgart, Porto), (Porto, Stuttgart),
    (Oslo, Split), (Split, Oslo),
    (Stockholm, Stuttgart), (Stuttgart, Stockholm),
    (Reykjavik, Oslo), (Oslo, Reykjavik),
    (Oslo, Geneva), (Geneva, Oslo),
    (Stockholm, Split), (Split, Stockholm),
    (Split, Stuttgart), (Stuttgart, Split),
    (Tallinn, Oslo), (Oslo, Tallinn),
    (Stockholm, Geneva), (Geneva, Stockholm),
    (Oslo, Porto), (Porto, Oslo),
    (Geneva, Porto), (Porto, Geneva),
    (Geneva, Split), (Split, Geneva),
]

# Add constraints for allowed transitions between consecutive cities
for i in range(7):
    transitions = []
    for a, b in allowed_pairs:
        transitions.append(And(cities_order[i] == a, cities_order[i+1] == b))
    solver.add(Or(transitions))

# Constraint for Stockholm's start day
for i in range(8):
    solver.add(Implies(cities_order[i] == Stockholm, start_day[i] <= 4))

# Check for solution
if solver.check() == sat:
    model = solver.model()
    cities_order_vals = [model.evaluate(c).name() for c in cities_order]
    start_day_vals = [model.evaluate(s).as_long() for s in start_day]
    end_day_vals = [model.evaluate(e).as_long() for e in end_day]
    
    # Generate itinerary
    itinerary = []
    for i in range(8):
        city = cities_order_vals[i]
        start = start_day_vals[i]
        end = end_day_vals[i]
        day_range = f"Day {start}-{end}"
        itinerary.append({"day_range": day_range, "place": city})
    
    print(json.dumps({"itinerary": itinerary}))
else:
    print("No solution found.")