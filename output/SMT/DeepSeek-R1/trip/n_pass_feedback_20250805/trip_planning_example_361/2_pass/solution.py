from z3 import *

# Define the cities and direct flights
cities = ['Paris', 'Madrid', 'Bucharest', 'Seville']
direct_flights = [
    ('Paris', 'Bucharest'),
    ('Seville', 'Paris'),
    ('Madrid', 'Bucharest'),
    ('Madrid', 'Paris'),
    ('Madrid', 'Seville')
]

# Create a set of allowed flight pairs (both directions)
allowed_pairs = set()
for a, b in direct_flights:
    allowed_pairs.add((a, b))
    allowed_pairs.add((b, a))

# Identify disallowed city pairs (cities without direct flights)
disallowed_pairs = []
for i in range(len(cities)):
    for j in range(i+1, len(cities)):
        if (cities[i], cities[j]) not in allowed_pairs:
            disallowed_pairs.append((i, j))

# Create Z3 solver and variables
s = Solver()
in_city = [[Bool(f'in_{i}_{city}') for city in cities] for i in range(1, 16)]

# Constraints for each day
for i in range(15):
    # At least one city per day
    s.add(Or(in_city[i]))
    # At most two cities per day
    s.add(Sum([If(in_city[i][j], 1, 0) for j in range(len(cities))]) <= 2)
    
    # Disallow pairs without direct flights
    for idx1, idx2 in disallowed_pairs:
        s.add(Or(Not(in_city[i][idx1]), Not(in_city[i][idx2])))

# Consecutive days must share at least one city
for i in range(14):
    common_constraints = [And(in_city[i][j], in_city[i+1][j]) for j in range(len(cities))]
    s.add(Or(common_constraints))

# Specific constraints
madrid_idx = cities.index('Madrid')
bucharest_idx = cities.index('Bucharest')
paris_idx = cities.index('Paris')
seville_idx = cities.index('Seville')

# Madrid from day 1 to 7
for i in range(7):
    s.add(in_city[i][madrid_idx] == True)

# Bucharest only on days 14 and 15
for i in range(13):
    s.add(in_city[i][bucharest_idx] == False)
s.add(in_city[13][bucharest_idx] == True)  # Day 14
s.add(in_city[14][bucharest_idx] == True)  # Day 15

# Only Bucharest on day 15
s.add(in_city[14][bucharest_idx] == True)
for j in [paris_idx, madrid_idx, seville_idx]:
    s.add(in_city[14][j] == False)

# Total days in Paris and Seville
total_paris = 0
for i in range(15):
    total_paris += If(in_city[i][paris_idx], 1, 0)
s.add(total_paris == 6)

total_seville = 0
for i in range(15):
    total_seville += If(in_city[i][seville_idx], 1, 0)
s.add(total_seville == 3)

# Solve the problem
if s.check() == sat:
    m = s.model()
    itinerary = []
    for i in range(15):
        day_cities = []
        for j, city in enumerate(cities):
            if m.evaluate(in_city[i][j]):
                day_cities.append(city)
        day_cities_sorted = sorted(day_cities)
        place_str = ", ".join(day_cities_sorted)
        itinerary.append({"day": i+1, "place": place_str})
    result = {"itinerary": itinerary}
    print(result)
else:
    print("No solution found")