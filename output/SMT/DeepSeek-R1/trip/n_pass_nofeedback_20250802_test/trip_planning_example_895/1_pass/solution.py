from z3 import *
import json

city_names = ['Brussels', 'Venice', 'London', 'Lisbon', 'Reykjavik', 'Santorini', 'Madrid']
n_cities = len(city_names)
n_days = 17

# Map city names to indices
city_index = {name: idx for idx, name in enumerate(city_names)}

# Define directed flights
directed_flights = set()

# Bidirectional flights
bidir = [
    ('Venice', 'Madrid'),
    ('Lisbon', 'Reykjavik'),
    ('Brussels', 'Venice'),
    ('Venice', 'Santorini'),
    ('Lisbon', 'Venice'),
    ('Brussels', 'London'),
    ('Madrid', 'London'),
    ('Santorini', 'London'),
    ('London', 'Reykjavik'),
    ('Brussels', 'Lisbon'),
    ('Lisbon', 'London'),
    ('Lisbon', 'Madrid'),
    ('Madrid', 'Santorini'),
    ('Brussels', 'Reykjavik'),
    ('Brussels', 'Madrid'),
    ('Venice', 'London')
]

for (a, b) in bidir:
    directed_flights.add((a, b))
    directed_flights.add((b, a))

# Unidirectional flight
directed_flights.add(('Reykjavik', 'Madrid'))

# Create a flight_ok matrix: flight_ok[i][j] is True if there's a flight from city i to city j
flight_ok_bool = [[False]*n_cities for _ in range(n_cities)]
for i in range(n_cities):
    for j in range(n_cities):
        if i == j:
            continue
        if (city_names[i], city_names[j]) in directed_flights:
            flight_ok_bool[i][j] = True

# Total days required per city: [Brussels, Venice, London, Lisbon, Reykjavik, Santorini, Madrid]
total_days = [2, 3, 3, 4, 3, 3, 5]

# Create Z3 variables: in_city[day][city]
in_city = [[Bool(f"in_city_d{d}_c{c}") for c in range(n_cities)] for d in range(n_days)]

s = Solver()

# Fixed constraints for Brussels: days 1 and 2 (index 0 and 1)
brussels_idx = city_index['Brussels']
s.add(in_city[0][brussels_idx] == True)
s.add(in_city[1][brussels_idx] == True)

# Fixed constraints for Madrid: days 7 to 11 (indices 6 to 10)
madrid_idx = city_index['Madrid']
for d in [6,7,8,9,10]:
    s.add(in_city[d][madrid_idx] == True)

# Day 0 (first day): only Brussels (since we start without any flight on day1)
for c in range(n_cities):
    if c != brussels_idx:
        s.add(in_city[0][c] == False)

# For each day: at least one and at most two cities
for d in range(n_days):
    # At least one city
    s.add(Or(in_city[d]))
    # At most two cities: use sum <= 2
    count = Sum([If(in_city[d][c], 1, 0) for c in range(n_cities)])
    s.add(count >= 1, count <= 2)

# Total days per city
for c in range(n_cities):
    total = Sum([If(in_city[d][c], 1, 0) for d in range(n_days)])
    s.add(total == total_days[c])

# Flight constraints for consecutive days (d from 1 to 16, representing days 2 to 17)
for d in range(1, n_days):
    # Same set condition: all cities same as previous day
    same_set = And([in_city[d-1][c] == in_city[d][c] for c in range(n_cities)])
    # Count of removed and added cities
    removed_count = Sum([If(And(in_city[d-1][c], Not(in_city[d][c])), 1, 0) for c in range(n_cities)])
    added_count = Sum([If(And(Not(in_city[d-1][c]), in_city[d][c]), 1, 0) for c in range(n_cities)])
    # Condition for flight: one removed and one added, with a direct flight from removed to added
    flight_conditions = []
    for A in range(n_cities):
        for B in range(n_cities):
            if A == B:
                continue
            if flight_ok_bool[A][B]:
                cond = And(
                    in_city[d-1][A], 
                    Not(in_city[d][A]),
                    Not(in_city[d-1][B]),
                    in_city[d][B]
                )
                flight_conditions.append(cond)
    # Add the constraint: either same_set or (one removed, one added, and a valid flight)
    s.add(Or(
        same_set,
        And(removed_count == 1, added_count == 1, Or(flight_conditions))
    ))

# Venice constraint: at least one day in [5,7] (indices 4,5,6)
venice_idx = city_index['Venice']
s.add(Or(in_city[4][venice_idx], in_city[5][venice_idx], in_city[6][venice_idx]))

# Solve
if s.check() == sat:
    m = s.model()
    itinerary = []
    for d in range(n_days):
        places = []
        for c in range(n_cities):
            if is_true(m.evaluate(in_city[d][c])):
                places.append(city_names[c])
        itinerary.append({"day": d+1, "place": places})
    result = {'itinerary': itinerary}
    print(json.dumps(result))
else:
    print("No solution found")