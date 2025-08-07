import z3
import json

# Define the City enum type
City, (Reykjavik, Stockholm, Oslo, Tallinn, Stuttgart, Split, Geneva, Porto) = \
    z3.EnumSort('City', ['Reykjavik', 'Stockholm', 'Oslo', 'Tallinn', 'Stuttgart', 'Split', 'Geneva', 'Porto'])

# Define the allowed direct flights (both directions)
allowed_flights_set = [
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

directed_flights = set()
for (a, b) in allowed_flights_set:
    directed_flights.add((a, b))
    directed_flights.add((b, a))

# Create variables for the end city of each day
y = [z3.Const(f'y{i}', City) for i in range(21)]

solver = z3.Solver()

# Fixed constraints
solver.add(y[0] == Reykjavik)  # Day 1 in Reykjavik
solver.add(y[18] == Porto)      # Day 19 in Porto
solver.add(y[19] == Porto)      # Day 20 in Porto
solver.add(y[20] == Porto)      # Day 21 in Porto
solver.add(z3.Or(y[1] == Stockholm, y[2] == Stockholm, y[3] == Stockholm))  # Meeting in Stockholm

# Flight constraints for transitions between days
for i in range(20):
    if_y_changed = y[i] != y[i+1]
    allowed_flight_conditions = [z3.And(y[i] == a, y[i+1] == b) for (a, b) in directed_flights]
    solver.add(z3.Implies(if_y_changed, z3.Or(allowed_flight_conditions)))

# Total days per city
def total_days(city):
    total = z3.If(y[0] == city, 1, 0)
    for i in range(1, 21):
        total = total + z3.If(z3.Or(y[i-1] == city, y[i] == city), 1, 0)
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
    y_vals = [model.eval(y_i) for y_i in y]
    
    itinerary = []
    # Day 1: only the end city (Reykjavik)
    day1_city = str(y_vals[0])
    itinerary.append({"day": 1, "city": [day1_city]})
    
    # Days 2 to 21: consider start and end cities
    for i in range(1, 21):
        start_city = y_vals[i-1]
        end_city = y_vals[i]
        if start_city == end_city:
            cities_list = [str(start_city)]
        else:
            cities_list = sorted([str(start_city), str(end_city)])
        itinerary.append({"day": i+1, "city": cities_list})
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))
else:
    print(json.dumps({"error": "No solution found"}))