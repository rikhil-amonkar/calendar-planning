from z3 import *

def solve_itinerary():
    s = Solver()

    # Cities and their indices
    cities = ['Madrid', 'Porto', 'Seville', 'Stuttgart']
    city_idx = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flight connections (bidirectional)
    connections = [
        (city_idx['Madrid'], city_idx['Porto']),
        (city_idx['Madrid'], city_idx['Seville']),
        (city_idx['Porto'], city_idx['Seville']),
        (city_idx['Porto'], city_idx['Stuttgart'])
    ]
    connections = connections + [(b,a) for (a,b) in connections]
    
    # Variables: For each day, track current city and whether flying
    max_days = 13
    current_city = [Int(f'city_day_{day}') for day in range(1, max_days+1)]
    is_flying = [Bool(f'fly_day_{day}') for day in range(1, max_days)]
    next_city = [Int(f'next_city_{day}') for day in range(1, max_days)]

    # Initial constraints
    s.add(current_city[0] == city_idx['Madrid'])  # Start in Madrid
    
    # Flight constraints
    for day in range(max_days-1):
        # If flying, next city must be connected to current
        s.add(Implies(is_flying[day], 
                     Or([And(current_city[day] == a, next_city[day] == b) 
                        for (a,b) in connections])))
        # If not flying, stay in same city
        s.add(Implies(Not(is_flying[day]), 
                     next_city[day] == current_city[day]))
        # Next day's city is the next city
        s.add(current_city[day+1] == next_city[day])

    # Count days in each city (including flight days)
    madrid_days = Sum([If(current_city[day] == city_idx['Madrid'], 1, 0) 
                     for day in range(max_days)])
    porto_days = Sum([If(current_city[day] == city_idx['Porto'], 1, 0) 
                    for day in range(max_days)])
    seville_days = Sum([If(current_city[day] == city_idx['Seville'], 1, 0) 
                     for day in range(max_days)])
    stuttgart_days = Sum([If(current_city[day] == city_idx['Stuttgart'], 1, 0) 
                      for day in range(max_days)])

    # Stay requirements
    s.add(madrid_days == 4)  # 4 days in Madrid (including days 1-4)
    s.add(porto_days == 3)   # 3 days in Porto
    s.add(seville_days == 2) # 2 days in Seville
    s.add(stuttgart_days == 7) # 7 days in Stuttgart
    
    # Mandatory days in Madrid (1-4) and Stuttgart (7,13)
    for day in [0,1,2,3]:  # Days 1-4 (0-indexed)
        s.add(current_city[day] == city_idx['Madrid'])
    s.add(Or(current_city[6] == city_idx['Stuttgart'],   # Day 7
             current_city[12] == city_idx['Stuttgart'])) # Day 13

    # Additional constraints to help solver
    # No flights on first 4 days (already in Madrid)
    for day in range(4):
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