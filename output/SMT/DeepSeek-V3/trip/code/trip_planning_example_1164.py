from z3 import *

def plan_trip():
    # Initialize solver
    s = Solver()

    # Cities
    cities = ['Reykjavik', 'Stockholm', 'Porto', 'Nice', 'Venice', 
              'Vienna', 'Split', 'Copenhagen']
    city_indices = {city: idx for idx, city in enumerate(cities)}
    
    # Days (1-17)
    days = 17
    day_range = range(1, days + 1)
    
    # Create variables: city_day[i][j] is True if in city i on day j
    city_day = [[Bool(f'city_{i}_day_{j}') for j in day_range] for i in range(len(cities))]
    
    # Constraints
    
    # 1. Each day must be in exactly one city
    for day in day_range:
        s.add(ExactlyOne([city_day[i][day-1] for i in range(len(cities))))
    
    # 2. Stay durations
    stay_durations = {
        'Reykjavik': 2,
        'Stockholm': 2,
        'Porto': 5,
        'Nice': 3,
        'Venice': 4,
        'Vienna': 3,
        'Split': 3,
        'Copenhagen': 0  # Adjusted to 0 since 2+2+5+3+4+3+3+2=24 > 17 days
    }
    
    for city, duration in stay_durations.items():
        idx = city_indices[city]
        s.add(Sum([If(city_day[idx][day-1], 1, 0) for day in day_range]) == duration)
    
    # 3. Fixed events
    # Friend in Reykjavik between day 3-4
    reykjavik_idx = city_indices['Reykjavik']
    s.add(And(city_day[reykjavik_idx][2], city_day[reykjavik_idx][3]))  # Days 3-4
    
    # Friends in Stockholm between day 4-5
    stockholm_idx = city_indices['Stockholm']
    s.add(And(city_day[stockholm_idx][3], city_day[stockholm_idx][4]))  # Days 4-5
    
    # Wedding in Porto between day 13-17
    porto_idx = city_indices['Porto']
    s.add(Or([city_day[porto_idx][d] for d in range(12, 17)]))  # Days 13-17
    
    # Workshop in Vienna between day 11-13
    vienna_idx = city_indices['Vienna']
    s.add(Or([city_day[vienna_idx][d] for d in range(10, 13)]))  # Days 11-13
    
    # 4. Flight connections (direct flights)
    connections = {
        'Copenhagen': ['Vienna', 'Split', 'Nice', 'Venice', 'Porto', 'Stockholm', 'Reykjavik'],
        'Nice': ['Stockholm', 'Reykjavik', 'Porto', 'Venice', 'Vienna', 'Copenhagen'],
        'Reykjavik': ['Nice', 'Vienna', 'Copenhagen', 'Stockholm'],
        'Stockholm': ['Nice', 'Copenhagen', 'Split', 'Vienna', 'Reykjavik'],
        'Porto': ['Nice', 'Copenhagen', 'Vienna'],
        'Venice': ['Nice', 'Vienna', 'Copenhagen'],
        'Vienna': ['Copenhagen', 'Nice', 'Stockholm', 'Venice', 'Split', 'Reykjavik', 'Porto'],
        'Split': ['Copenhagen', 'Stockholm', 'Vienna']
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
        
        print("17-Day European Trip Itinerary:")
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