from z3 import *

def solve_itinerary():
    s = Solver()

    # Cities and indices
    cities = ['Madrid', 'Porto', 'Seville', 'Stuttgart']
    city_idx = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flight connections (bidirectional)
    connections = [
        (city_idx['Madrid'], city_idx['Porto']),
        (city_idx['Madrid'], city_idx['Seville']),
        (city_idx['Porto'], city_idx['Seville']),
        (city_idx['Porto'], city_idx['Stuttgart'])
    ]
    connections += [(b,a) for (a,b) in connections]  # Make bidirectional

    # Variables for each day
    max_days = 13
    current_city = [Int(f'city_{day}') for day in range(max_days)]
    is_flying = [Bool(f'fly_{day}') for day in range(max_days-1)]
    next_city = [Int(f'next_{day}') for day in range(max_days-1)]

    # Initial constraints
    s.add(current_city[0] == city_idx['Madrid'])  # Start in Madrid on day 1
    
    # Flight constraints
    for day in range(max_days-1):
        # If flying, next city must be connected
        s.add(Implies(is_flying[day],
            Or([And(current_city[day] == a, next_city[day] == b) for (a,b) in connections])))
        # If not flying, stay in same city
        s.add(Implies(Not(is_flying[day]), next_city[day] == current_city[day]))
        # Next day's city is the next city
        s.add(current_city[day+1] == next_city[day])

    # Count days in each city (including flight days)
    counts = {city: 0 for city in cities}
    for city in cities:
        counts[city] = Sum([If(current_city[day] == city_idx[city], 1, 0) 
                         for day in range(max_days)])

    # Stay requirements
    s.add(counts['Madrid'] == 4)
    s.add(counts['Porto'] == 3)
    s.add(counts['Seville'] == 2)
    s.add(counts['Stuttgart'] == 7)

    # Mandatory days
    s.add(current_city[0] == city_idx['Madrid'])  # Day 1
    s.add(current_city[1] == city_idx['Madrid'])  # Day 2
    s.add(current_city[2] == city_idx['Madrid'])  # Day 3
    s.add(current_city[3] == city_idx['Madrid'])  # Day 4
    s.add(Or(current_city[6] == city_idx['Stuttgart'],   # Day 7
             current_city[12] == city_idx['Stuttgart'])) # Day 13

    # Additional constraints to help solver
    # No flights during first 4 days in Madrid
    for day in range(3):  # Days 1-3 (since we can fly on day 4)
        s.add(Not(is_flying[day]))

    # Try to find solution
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for day in range(max_days):
            city = cities[m[current_city[day]].as_long()]
            if day < max_days-1 and m[is_flying[day]]:
                next_c = cities[m[next_city[day]].as_long()]
                itinerary.append({'day': day+1, 'cities': [city, next_c]})
            else:
                itinerary.append({'day': day+1, 'cities': [city]})
        return {'itinerary': itinerary}
    else:
        return None

# Solve and print
result = solve_itinerary()
if result:
    print(result)
else:
    print("No valid itinerary found")