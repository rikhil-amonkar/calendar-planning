import z3
import json

# Define the City enum type
City, (Reykjavik, Stockholm, Oslo, Tallinn, Stuttgart, Split, Geneva, Porto) = \
    z3.EnumSort('City', ['Reykjavik', 'Stockholm', 'Oslo', 'Tallinn', 'Stuttgart', 'Split', 'Geneva', 'Porto'])

# Define the allowed direct flights (both directions)
allowed_flights = [
    (Reykjavik, Stuttgart),
    (Reykjavik, Stockholm),
    (Reykjavik, Tallinn),
    (Stockholm, Oslo),
    (Stuttgart, Porto),
    (Oslo, Split),
    (Stockholm, Stuttgart),
    (Reykjavik, Oslo),
    (Oslo, Geneva),
    (Stockholm, Split),
    (Split, Stuttgart),
    (Tallinn, Oslo),
    (Stockholm, Geneva),
    (Oslo, Porto),
    (Geneva, Porto),
    (Geneva, Split)
]

allowed_pairs = set()
for a, b in allowed_flights:
    allowed_pairs.add((a, b))
    allowed_pairs.add((b, a))

# Create variables for the end city of each day (21 days)
c = [z3.Const(f'c_{i}', City) for i in range(21)]

solver = z3.Solver()

# Fixed constraints
solver.add(c[0] == Reykjavik)  # Day 1 must end in Reykjavik
solver.add(c[18] == Porto)      # Day 19 must end in Porto
solver.add(c[19] == Porto)      # Day 20 must end in Porto
solver.add(c[20] == Porto)      # Day 21 must end in Porto

# Meeting in Stockholm between day 2 and day 4 (days 2,3,4 in 1-indexing)
solver.add(z3.Or(c[1] == Stockholm, c[2] == Stockholm, c[3] == Stockholm))

# Flight constraints: consecutive days must be either the same city or connected by a direct flight
for i in range(20):
    solver.add(z3.Or(
        c[i] == c[i+1],
        z3.Or([z3.And(c[i] == a, c[i+1] == b) for (a, b) in allowed_pairs])
    ))

# Total days per city
def total_days(city):
    total = z3.If(c[0] == city, 1, 0)
    for i in range(1, 21):
        total = total + z3.If(z3.Or(c[i-1] == city, c[i] == city), 1, 0)
    return total

solver.add(total_days(Reykjavik) == 2)
solver.add(total_days(Oslo) == 5)
solver.add(total_days(Stuttgart) == 5)
solver.add(total_days(Split) == 3)
solver.add(total_days(Geneva) == 2)
solver.add(total_days(Porto) == 3)
solver.add(total_days(Tallinn) == 5)
solver.add(total_days(Stockholm) == 3)

# Solve the problem
if solver.check() == z3.sat:
    model = solver.model()
    c_vals = [model.eval(c_i) for c_i in c]
    
    itinerary = []
    # Day 1
    day1_city = str(c_vals[0])
    itinerary.append({"day": 1, "city": [day1_city]})
    
    # Days 2 to 21
    for i in range(1, 21):
        start_city = c_vals[i-1]
        end_city = c_vals[i]
        if start_city.eq(end_city):
            cities_list = [str(start_city)]
        else:
            cities_list = sorted([str(start_city), str(end_city)])
        itinerary.append({"day": i+1, "city": cities_list})
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))
else:
    print(json.dumps({"error": "No solution found"}))