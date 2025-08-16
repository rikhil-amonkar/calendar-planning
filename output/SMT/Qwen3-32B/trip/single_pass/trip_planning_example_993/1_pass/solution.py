import z3
import json

# Define cities and their indices
cities = ['Riga', 'Frankfurt', 'Amsterdam', 'Vilnius', 'London', 'Stockholm', 'Bucharest']
required_days = {
    0: 2,   # Riga
    1: 3,   # Frankfurt
    2: 2,   # Amsterdam
    3: 5,   # Vilnius
    4: 2,   # London
    5: 3,   # Stockholm
    6: 4,   # Bucharest
}

# Define allowed flights as pairs (from, to)
allowed_flights = set()
# London and Amsterdam
allowed_flights.add((4, 2))
allowed_flights.add((2, 4))
# Vilnius and Frankfurt
allowed_flights.add((3, 1))
allowed_flights.add((1, 3))
# Riga to Vilnius
allowed_flights.add((0, 3))
allowed_flights.add((3, 0))
# Riga and Stockholm
allowed_flights.add((0, 5))
allowed_flights.add((5, 0))
# London and Bucharest
allowed_flights.add((4, 6))
allowed_flights.add((6, 4))
# Amsterdam and Stockholm
allowed_flights.add((2, 5))
allowed_flights.add((5, 2))
# Amsterdam and Frankfurt
allowed_flights.add((2, 1))
allowed_flights.add((1, 2))
# Frankfurt and Stockholm
allowed_flights.add((1, 5))
allowed_flights.add((5, 1))
# Bucharest and Riga
allowed_flights.add((6, 0))
allowed_flights.add((0, 6))
# Amsterdam and Riga
allowed_flights.add((2, 0))
allowed_flights.add((0, 2))
# Amsterdam and Bucharest
allowed_flights.add((2, 6))
allowed_flights.add((6, 2))
# Riga and Frankfurt
allowed_flights.add((0, 1))
allowed_flights.add((1, 0))
# Bucharest and Frankfurt
allowed_flights.add((6, 1))
allowed_flights.add((1, 6))
# London and Frankfurt
allowed_flights.add((4, 1))
allowed_flights.add((1, 4))
# London and Stockholm
allowed_flights.add((4, 5))
allowed_flights.add((5, 4))
# Amsterdam and Vilnius
allowed_flights.add((2, 3))
allowed_flights.add((3, 2))

# Create Z3 variables for each day (1-15)
days = 15
city = [z3.Int(f'city_{d}') for d in range(days)]  # city[0] is day 1, ..., city[14] is day 15

s = z3.Solver()

# Each day's city is between 0 and 6
for d in city:
    s.add(z3.And(d >= 0, d <= 6))

# Consecutive days must have allowed flights
allowed_pairs = list(allowed_flights)
for d in range(days - 1):  # 0 to 13 (days 1-14)
    current = city[d]
    next_c = city[d + 1]
    constraints = []
    for a, b in allowed_pairs:
        constraints.append(z3.And(current == a, next_c == b))
    s.add(z3.Or(*constraints))

# Constraints for required days in each city
for c in range(7):
    sum_current = 0
    sum_arrival = 0
    for d in range(days):
        # Sum current
        sum_current += z3.If(city[d] == c, 1, 0)
        # Sum arrival
        if d == 0:
            sum_arrival += 0
        else:
            sum_arrival += z3.If(z3.And(city[d] == c, city[d-1] != c), 1, 0)
    s.add(sum_current + sum_arrival == required_days[c])

# Event constraints
# Amsterdam between day 2 and 3 (day indices 1 and 2)
s.add(z3.Or(city[1] == 2, city[2] == 2))
# Vilnius between day 7 and 11 (indices 6 to 10)
s.add(z3.Or(city[6] == 3, city[7] == 3, city[8] == 3, city[9] == 3, city[10] == 3))
# Stockholm between day 13 and 15 (indices 12, 13, 14)
s.add(z3.Or(city[12] == 5, city[13] == 5, city[14] == 5))

# Check if the constraints are satisfiable
if s.check() == z3.sat:
    model = s.model()
    # Extract the cities for each day
    itinerary = []
    for d in range(days):
        city_index = model[city[d]].as_long()
        itinerary.append({'day': d + 1, 'city': cities[city_index]})
    # Format as JSON
    output = {'itinerary': itinerary}
    print(json.dumps(output, indent=2))
else:
    print("No solution found.")