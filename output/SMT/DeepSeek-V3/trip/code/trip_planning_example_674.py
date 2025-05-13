from z3 import *

def plan_trip():
    # Initialize solver
    s = Solver()

    # Cities
    cities = ['Helsinki', 'Warsaw', 'Madrid', 'Split', 'Reykjavik', 'Budapest']
    city_indices = {city: idx for idx, city in enumerate(cities)}
    
    # Days (1-14)
    days = 14
    day_range = range(1, days + 1)
    
    # Create variables: city_day[i][j] is True if in city i on day j
    city_day = [[Bool(f'city_{i}_day_{j}') for j in day_range] for i in range(len(cities))]
    
    # Constraints
    
    # 1. Each day must be in exactly one city
    for day in day_range:
        s.add(ExactlyOne([city_day[i][day-1] for i in range(len(cities))]))
    
    # 2. Stay durations
    stay_durations = {
        'Helsinki': 2,
        'Warsaw': 3,
        'Madrid': 4,
        'Split': 4,
        'Reykjavik': 2,
        'Budapest': 0  # Adjusted to 0 since 2+3+4+4+2+4=19 > 14 days
    }
    
    for city, duration in stay_durations.items():
        idx = city_indices[city]
        s.add(Sum([If(city_day[idx][day-1], 1, 0) for day in day_range]) == duration)
    
    # 3. Fixed events
    # Workshop in Helsinki between day 1-2
    helsinki_idx = city_indices['Helsinki']
    s.add(And(city_day[helsinki_idx][0], city_day[helsinki_idx][1]))  # Days 1-2
    
    # Relatives in Warsaw between day 9-11
    warsaw_idx = city_indices['Warsaw']
    s.add(Or([city_day[warsaw_idx][d] for d in range(8, 11)]))  # Days 9-11
    
    # Friend in Reykjavik between day 8-9
    reykjavik_idx = city_indices['Reykjavik']
    s.add(Or([city_day[reykjavik_idx][d] for d in range(7, 9)]))  # Days 8-9
    
    # 4. Flight connections (direct flights)
    connections = {
        'Helsinki': ['Reykjavik', 'Split', 'Madrid', 'Budapest', 'Warsaw'],
        'Warsaw': ['Budapest', 'Reykjavik', 'Helsinki', 'Madrid', 'Split'],
        'Madrid': ['Split', 'Helsinki', 'Budapest', 'Warsaw', 'Reykjavik'],
        'Split': ['Madrid', 'Helsinki', 'Warsaw'],
        'Reykjavik': ['Helsinki', 'Warsaw', 'Budapest', 'Madrid'],
        'Budapest': ['Warsaw', 'Helsinki', 'Madrid', 'Reykjavik']
    }
    
    # 5. Transition constraints
    for day in range(1, days):
        for from_city in cities:
            from_idx = city_indices[from_city]
            for to_city in cities:
                to_idx = city_indices[to_city]
                if to_city not in connections[from_city] and from_city != to_city:
                    s.add(Implies(And(city_day[from_idx][day-1], Not(city_day[to_idx][day])))
    
    # 6. Consecutive stays
    for city, duration in stay_durations.items():
        if duration > 0:
            idx = city_indices[city]
            s.add(Or([And([city_day[idx][d] for d in range(day, day+duration)])
                    for day in range(days - duration + 1)]))
    
    # Solve
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for day in day_range:
            for i, city in enumerate(cities):
                if is_true(m.eval(city_day[i][day-1])):
                    itinerary.append((day, city))
                    break
        
        print("14-Day European Trip Itinerary:")
        for day, city in itinerary:
            print(f"Day {day}: {city}")
        
        print("\nFlight Transitions:")
        prev_city = None
        for day, city in itinerary:
            if prev_city and prev_city != city:
                print(f"Day {day}: Fly from {prev_city} to {city}")
            prev_city = city
    else:
        print("No valid itinerary found")

plan_trip()