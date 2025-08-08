from z3 import *

# Define cities and direct flight connections
cities = ['Paris', 'Madrid', 'Bucharest', 'Seville']
direct_flights = [
    ('Paris', 'Bucharest'),
    ('Seville', 'Paris'),
    ('Madrid', 'Bucharest'),
    ('Madrid', 'Paris'),
    ('Madrid', 'Seville')
]

# Create allowed flight pairs (bidirectional)
allowed_pairs = set()
for a, b in direct_flights:
    allowed_pairs.add((a, b))
    allowed_pairs.add((b, a))

# Identify disallowed city pairs (no direct flight)
disallowed_pairs = []
for i in range(len(cities)):
    for j in range(i+1, len(cities)):
        if (cities[i], cities[j]) not in allowed_pairs:
            disallowed_pairs.append((i, j))

# Initialize Z3 solver and variables
s = Solver()
in_city = [[Bool(f'in_{i}_{city}') for city in cities] for i in range(1, 16)]

# Constraints for each day
for i in range(15):
    # At least one city per day
    s.add(Or(in_city[i]))
    # At most two cities per day
    s.add(Sum([If(in_city[i][j], 1, 0) for j in range(len(cities))]) <= 2)
    
    # Disallow city pairs without direct flights
    for idx1, idx2 in disallowed_pairs:
        s.add(Or(Not(in_city[i][idx1]), Not(in_city[i][idx2])))

# Consecutive days must share at least one city
for i in range(14):
    common_constraints = [And(in_city[i][j], in_city[i+1][j]) for j in range(len(cities))]
    s.add(Or(common_constraints))

# City indices
madrid_idx = cities.index('Madrid')
bucharest_idx = cities.index('Bucharest')
paris_idx = cities.index('Paris')
seville_idx = cities.index('Seville')

# Madrid must be present from Day 1 to Day 7
for i in range(7):
    s.add(in_city[i][madrid_idx] == True)

# Bucharest must be present on Day 14 and 15
s.add(in_city[13][bucharest_idx] == True)  # Day 14
s.add(in_city[14][bucharest_idx] == True)  # Day 15
# Only Bucharest on Day 15
s.add(in_city[14][paris_idx] == False)
s.add(in_city[14][madrid_idx] == False)
s.add(in_city[14][seville_idx] == False)

# Seville constraints
# Absent on Days 1-5
for i in range(5):
    s.add(in_city[i][seville_idx] == False)
# Present on Days 6 and 7
s.add(in_city[5][seville_idx] == True)  # Day 6
s.add(in_city[6][seville_idx] == True)  # Day 7
# Exactly one more day in Seville between Days 8-13
s.add(Sum([If(in_city[i][seville_idx], 1, 0) for i in range(7, 13)]) == 1)

# Total days in Paris must be 6
total_paris = 0
for i in range(15):
    total_paris += If(in_city[i][paris_idx], 1, 0)
s.add(total_paris == 6)

# Solve and output itinerary
if s.check() == sat:
    m = s.model()
    # Build day-by-day itinerary
    daily_places = []
    for i in range(15):
        cities_today = []
        for j, city in enumerate(cities):
            if is_true(m.evaluate(in_city[i][j])):
                cities_today.append(city)
        daily_places.append(sorted(cities_today))
    
    # Group consecutive days with identical city sets
    itinerary = []
    start_day = 1
    current_places = daily_places[0]
    for i in range(1, 15):
        if daily_places[i] != current_places:
            end_day = i
            day_range = f"Day {start_day}-{end_day}" if start_day != end_day else f"Day {start_day}"
            itinerary.append({'day_range': day_range, 'place': ', '.join(current_places)})
            start_day = i + 1
            current_places = daily_places[i]
    # Add last segment
    end_day = 15
    day_range = f"Day {start_day}-{end_day}" if start_day != end_day else f"Day {start_day}"
    itinerary.append({'day_range': day_range, 'place': ', '.join(current_places)})
    
    print("Plan found:", {'itinerary': itinerary})
else:
    print("No solution found")