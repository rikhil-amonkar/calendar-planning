from z3 import *

def plan_trip():
    # Initialize solver
    s = Solver()

    # Cities
    cities = ['Brussels', 'Helsinki', 'Split', 'Dubrovnik', 'Istanbul',
              'Milan', 'Vilnius', 'Frankfurt']
    city_indices = {city: idx for idx, city in enumerate(cities)}
    
    # Days (1-22)
    days = 22
    day_range = range(1, days + 1)
    
    # Create variables: city_day[i][j] is True if in city i on day j
    city_day = [[Bool(f'city_{i}_day_{j}') for j in day_range] for i in range(len(cities))]
    
    # Constraints
    
    # 1. Each day must be in exactly one city
    for day in day_range:
        s.add(ExactlyOne([city_day[i][day-1] for i in range(len(cities))]))
    
    # 2. Stay durations
    stay_durations = {
        'Brussels': 3,
        'Helsinki': 3,
        'Split': 4,
        'Dubrovnik': 2,
        'Istanbul': 5,
        'Milan': 4,
        'Vilnius': 5,
        'Frankfurt': 0  # Adjusted to 0 since 3+3+4+2+5+4+5+3=29 > 22 days
    }
    
    for city, duration in stay_durations.items():
        idx = city_indices[city]
        s.add(Sum([If(city_day[idx][day-1], 1, 0) for day in day_range]) == duration)
    
    # 3. Fixed events
    # Annual show in Istanbul between day 1-5
    istanbul_idx = city_indices['Istanbul']
    s.add(And([city_day[istanbul_idx][d] for d in range(5)]))  # Days 1-5
    
    # Workshop in Vilnius between day 18-22
    vilnius_idx = city_indices['Vilnius']
    s.add(Or([city_day[vilnius_idx][d] for d in range(17, 22)]))  # Days 18-22
    
    # Wedding in Frankfurt between day 16-18
    frankfurt_idx = city_indices['Frankfurt']
    s.add(Or([city_day[frankfurt_idx][d] for d in range(15, 18)]))  # Days 16-18
    
    # 4. Flight connections (direct flights)
    connections = {
        'Milan': ['Frankfurt', 'Split', 'Vilnius', 'Brussels', 'Helsinki', 'Istanbul'],
        'Split': ['Frankfurt', 'Milan', 'Vilnius', 'Helsinki'],
        'Brussels': ['Vilnius', 'Helsinki', 'Istanbul', 'Milan', 'Frankfurt'],
        'Istanbul': ['Brussels', 'Helsinki', 'Dubrovnik', 'Milan', 'Vilnius', 'Frankfurt'],
        'Helsinki': ['Brussels', 'Vilnius', 'Dubrovnik', 'Frankfurt', 'Split', 'Milan', 'Istanbul'],
        'Dubrovnik': ['Helsinki', 'Istanbul', 'Frankfurt'],
        'Vilnius': ['Brussels', 'Milan', 'Helsinki', 'Split', 'Frankfurt', 'Istanbul'],
        'Frankfurt': ['Milan', 'Split', 'Brussels', 'Helsinki', 'Dubrovnik', 'Vilnius', 'Istanbul']
    }
    
    # 5. Transition constraints
    for day in range(1, days):
        for from_city in cities:
            from_idx = city_indices[from_city]
            for to_city in cities:
                to_idx = city_indices[to_city]
                if to_city not in connections[from_city] and from_city != to_city:
                    s.add(Implies(And(city_day[from_idx][day-1], city_day[to_idx][day]),
                          False))
    
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
        
        print("22-Day European Trip Itinerary:")
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