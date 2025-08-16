import z3
import json

cities = ['Santorini', 'Krakow', 'Paris', 'Vilnius', 'Munich', 'Geneva', 'Amsterdam', 'Budapest', 'Split']
city_indices = {name: i for i, name in enumerate(cities)}
durations = [5, 5, 5, 3, 5, 2, 4, 5, 4]  # [Santorini, Krakow, Paris, Vilnius, Munich, Geneva, Amsterdam, Budapest, Split]

allowed_flights = set()

# Adding all bidirectional flights as per the problem's list
allowed_flights.add( (2, 1) )
allowed_flights.add( (1, 2) )
allowed_flights.add( (2, 6) )
allowed_flights.add( (6, 2) )
allowed_flights.add( (2, 8) )
allowed_flights.add( (8, 2) )
allowed_flights.add( (3, 4) )
allowed_flights.add( (4, 3) )
allowed_flights.add( (2, 5) )
allowed_flights.add( (5, 2) )
allowed_flights.add( (6, 5) )
allowed_flights.add( (5, 6) )
allowed_flights.add( (4, 8) )
allowed_flights.add( (8, 4) )
allowed_flights.add( (8, 1) )
allowed_flights.add( (1, 8) )
allowed_flights.add( (4, 6) )
allowed_flights.add( (6, 4) )
allowed_flights.add( (7, 6) )
allowed_flights.add( (6, 7) )
allowed_flights.add( (8, 5) )
allowed_flights.add( (5, 8) )
allowed_flights.add( (3, 8) )
allowed_flights.add( (8, 3) )
allowed_flights.add( (4, 5) )
allowed_flights.add( (5, 4) )
allowed_flights.add( (4, 1) )
allowed_flights.add( (1, 4) )
allowed_flights.add( (1, 3) )
allowed_flights.add( (3, 1) )
allowed_flights.add( (3, 6) )
allowed_flights.add( (6, 3) )
allowed_flights.add( (7, 2) )
allowed_flights.add( (2, 7) )
allowed_flights.add( (1, 6) )
allowed_flights.add( (6, 1) )
allowed_flights.add( (3, 2) )
allowed_flights.add( (2, 3) )
allowed_flights.add( (7, 5) )
allowed_flights.add( (5, 7) )
allowed_flights.add( (8, 6) )
allowed_flights.add( (6, 8) )
allowed_flights.add( (0, 5) )
allowed_flights.add( (5, 0) )
allowed_flights.add( (6, 0) )
allowed_flights.add( (0, 6) )
allowed_flights.add( (4, 7) )
allowed_flights.add( (7, 4) )
allowed_flights.add( (4, 2) )
allowed_flights.add( (2, 4) )

solver = z3.Solver()

# Variables for the sequence of cities (each is an integer between 0 and 8, all distinct)
city_vars = [z3.Int(f'city_{i}') for i in range(9)]

# Variables for the start days of each city
start_day_vars = [z3.Int(f'start_day_{i}') for i in range(9)]

# Constraints for cities being distinct and in range
solver.add(z3.Distinct(city_vars))
for var in city_vars:
    solver.add(z3.And(0 <= var, var <= 8))

# Constraints for allowed flights between consecutive cities
for i in range(8):
    current_city = city_vars[i]
    next_city = city_vars[i+1]
    # Create a list of allowed (a, b) pairs
    allowed_pairs = [z3.And(current_city == a, next_city == b) for a, b in allowed_flights]
    solver.add(z3.Or(allowed_pairs))

# Constraints for start_day recurrence
for i in range(8):
    current_city = city_vars[i]
    duration = durations[current_city]
    solver.add(start_day_vars[i+1] == start_day_vars[i] + duration - 1)

# Constraint for the last day
last_city = city_vars[8]
solver.add(start_day_vars[8] + durations[last_city] -1 == 30)

# Constraints for start_day ranges based on city
for i in range(9):
    city = city_vars[i]
    start_day = start_day_vars[i]
    duration = durations[city]
    end_day = start_day + duration - 1
    # General constraints: start_day >=1 and end_day <=30
    solver.add(z3.And(start_day >= 1, end_day <= 30))
    # Specific constraints for certain cities
    # Santorini (0)
    solver.add(z3.Implies(city == 0, z3.And(start_day >= 21, start_day <= 26)))
    # Krakow (1)
    solver.add(z3.Implies(city == 1, z3.And(start_day >= 14, start_day <= 22)))
    # Paris (2)
    solver.add(z3.Implies(city == 2, z3.And(start_day >= 7, start_day <= 15)))

if solver.check() == z3.sat:
    model = solver.model()
    sequence = [model.evaluate(city_vars[i]).as_long() for i in range(9)]
    start_days = [model.evaluate(start_day_vars[i]).as_long() for i in range(9)]
    
    # Generate the itinerary
    itinerary = {}
    for i in range(9):
        city_index = sequence[i]
        city_name = cities[city_index]
        start = start_days[i]
        duration = durations[city_index]
        end = start + duration - 1
        for day in range(start, end + 1):
            itinerary[day] = city_name
    
    # Now, create the JSON output
    output = {'itinerary': [{'day': day, 'city': city} for day, city in sorted(itinerary.items())]}
    print(json.dumps(output, indent=2))
else:
    print("No solution found.")