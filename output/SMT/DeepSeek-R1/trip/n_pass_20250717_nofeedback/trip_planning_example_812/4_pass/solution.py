from z3 import *
import json

# Define the City datatype
City = Datatype('City')
City.declare('Paris')
City.declare('Florence')
City.declare('Vienna')
City.declare('Porto')
City.declare('Munich')
City.declare('Nice')
City.declare('Warsaw')
City = City.create()

# List of all cities
all_cities = [City.Paris, City.Florence, City.Vienna, City.Porto, City.Munich, City.Nice, City.Warsaw]

# Direct flights as tuples (both directions included)
pairs = [
    (City.Florence, City.Vienna),
    (City.Paris, City.Warsaw),
    (City.Munich, City.Vienna),
    (City.Porto, City.Vienna),
    (City.Warsaw, City.Vienna),
    (City.Florence, City.Munich),
    (City.Munich, City.Warsaw),
    (City.Munich, City.Nice),
    (City.Paris, City.Florence),
    (City.Warsaw, City.Nice),
    (City.Porto, City.Munich),
    (City.Porto, City.Nice),
    (City.Paris, City.Vienna),
    (City.Nice, City.Vienna),
    (City.Porto, City.Paris),
    (City.Paris, City.Nice),
    (City.Paris, City.Munich),
    (City.Porto, City.Warsaw)
]

direct_flights_set = set()
for (a, b) in pairs:
    direct_flights_set.add((a, b))
    direct_flights_set.add((b, a))

# Create Z3 solver
solver = Solver()

# Create city_end variables for 20 days: index 1 to 20
city_end = [None]  # index 0 unused
for d in range(1, 21):
    var_name = 'city_end_%d' % d
    city_end.append(Const(var_name, City))

# Constraint: Start in Porto on day 1
solver.add(city_end[1] == City.Porto)

# Define visited[d][c] for each day d and each city c
visited = {}
for d in range(1, 21):
    for c in all_cities:
        if d == 1:
            # On day 1, only the end city is visited
            visited[d, c] = (city_end[d] == c)
        else:
            # On other days, the city is visited if it's the end city or we left it that day
            visited[d, c] = Or(city_end[d] == c, And(city_end[d-1] == c, city_end[d] != city_end[d-1]))

# Fixed constraints: Porto on days 1,2,3
for d in [1,2,3]:
    solver.add(visited[d, City.Porto] == True)

# Fixed constraints: Warsaw on days 13,14,15
for d in [13,14,15]:
    solver.add(visited[d, City.Warsaw] == True)

# Fixed constraints: Vienna on days 19,20
for d in [19,20]:
    solver.add(visited[d, City.Vienna] == True)

# Total days per city
total_days = {}
for city in all_cities:
    total_days[city] = 0
    for d in range(1,21):
        total_days[city] += If(visited[d, city], 1, 0)

solver.add(total_days[City.Paris] == 5)
solver.add(total_days[City.Florence] == 3)
solver.add(total_days[City.Vienna] == 2)
solver.add(total_days[City.Porto] == 3)
solver.add(total_days[City.Munich] == 5)
solver.add(total_days[City.Nice] == 5)
solver.add(total_days[City.Warsaw] == 3)

# Flight constraints: for days 2 to 20, if city_end changes, the pair must be in direct_flights_set
for d in range(2, 21):
    c_prev = city_end[d-1]
    c_curr = city_end[d]
    # If the end city changes from previous day to current day, then the pair must be in the direct_flights_set
    cond = (c_prev != c_curr)
    allowed_pairs = []
    for (c1, c2) in direct_flights_set:
        allowed_pairs.append(And(c_prev == c1, c_curr == c2))
    solver.add(Implies(cond, Or(allowed_pairs)))

# Contiguous stay constraints
for city in all_cities:
    # Variables for first and last day of visit
    first_day = Int(f'first_{city}')
    last_day = Int(f'last_{city}')
    
    # Set initial domain
    solver.add(first_day >= 1, first_day <= 20)
    solver.add(last_day >= 1, last_day <= 20)
    solver.add(first_day <= last_day)
    
    # Constrain first_day to be first day visited
    for d in range(1, 21):
        solver.add(Implies(visited[d, city], first_day <= d))
        solver.add(Implies(And(d < first_day, d >= 1), Not(visited[d, city])))
    
    # Constrain last_day to be last day visited
    for d in range(1, 21):
        solver.add(Implies(visited[d, city], d <= last_day))
        solver.add(Implies(And(d > last_day, d <= 20), Not(visited[d, city])))
    
    # All days between first and last must be visited
    for d in range(1, 21):
        solver.add(Implies(And(first_day <= d, d <= last_day), visited[d, city]))

# Check and get model
if solver.check() == sat:
    m = solver.model()
    
    # Collect all visited days per city
    city_days = {city: [] for city in all_cities}
    for d in range(1, 21):
        for city in all_cities:
            if is_true(m.eval(visited[d, city])):
                city_days[city].append(d)
    
    # Create itinerary with contiguous ranges
    itinerary = []
    for city in all_cities:
        days = sorted(city_days[city])
        if not days:
            continue
            
        # Find contiguous ranges
        ranges = []
        start = days[0]
        end = days[0]
        for day in days[1:]:
            if day == end + 1:
                end = day
            else:
                ranges.append((start, end))
                start = day
                end = day
        ranges.append((start, end))
        
        # Format ranges
        for (start, end) in ranges:
            if start == end:
                day_range = f"Day {start}"
            else:
                day_range = f"Day {start}-{end}"
            itinerary.append({
                "day_range": day_range,
                "place": str(city)
            })
    
    # Sort itinerary by start day
    itinerary.sort(key=lambda x: int(x['day_range'].split(' ')[1].split('-')[0]))
    
    # Output as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    print("No solution found")