from z3 import *

def plan_trip():
    # Initialize solver
    s = Solver()

    # Cities
    cities = ['Oslo', 'Reykjavik', 'Stockholm', 'Munich', 'Frankfurt', 'Barcelona', 'Bucharest', 'Split']
    city_indices = {city: idx for idx, city in enumerate(cities)}
    
    # Days (1-20)
    days = 20
    day_range = range(1, days + 1)
    
    # Create variables: city_day[i][j] is True if in city i on day j
    city_day = [[Bool(f'city_{i}_day_{j}') for j in day_range] for i in range(len(cities))]
    
    # Constraints
    
    # 1. Each day must be in exactly one city
    for day in day_range:
        s.add(ExactlyOne([city_day[i][day-1] for i in range(len(cities))]))
    
    # 2. Stay durations
    stay_durations = {
        'Oslo': 2,
        'Reykjavik': 5,
        'Stockholm': 4,
        'Munich': 4,
        'Frankfurt': 4,
        'Barcelona': 3,
        'Bucharest': 2,
        'Split': 3
    }
    
    for city, duration in stay_durations.items():
        idx = city_indices[city]
        # Total days in city must equal duration
        s.add(Sum([If(city_day[idx][day-1], 1, 0) for day in day_range]) == duration)
    
    # 3. Fixed events
    # Annual show in Oslo between day 16-17
    oslo_idx = city_indices['Oslo']
    s.add(And(city_day[oslo_idx][15], city_day[oslo_idx][16]))  # Days 16-17
    
    # Friend in Reykjavik between day 9-13
    reykjavik_idx = city_indices['Reykjavik']
    s.add(Or([city_day[reykjavik_idx][d] for d in range(8, 13)]))  # Days 9-13
    
    # Relatives in Munich between day 13-16
    munich_idx = city_indices['Munich']
    s.add(Or([city_day[munich_idx][d] for d in range(12, 16)]))  # Days 13-16
    
    # Workshop in Frankfurt between day 17-20
    frankfurt_idx = city_indices['Frankfurt']
    s.add(Or([city_day[frankfurt_idx][d] for d in range(16, 20)]))  # Days 17-20
    
    # 4. Flight connections (direct flights)
    connections = {
        'Reykjavik': ['Munich', 'Oslo', 'Frankfurt', 'Stockholm', 'Barcelona'],
        'Munich': ['Frankfurt', 'Reykjavik', 'Bucharest', 'Stockholm', 'Oslo', 'Barcelona', 'Split'],
        'Frankfurt': ['Munich', 'Oslo', 'Barcelona', 'Bucharest', 'Reykjavik', 'Stockholm', 'Split'],
        'Barcelona': ['Frankfurt', 'Bucharest', 'Stockholm', 'Reykjavik', 'Oslo', 'Split', 'Munich'],
        'Bucharest': ['Munich', 'Barcelona', 'Oslo', 'Frankfurt'],
        'Stockholm': ['Reykjavik', 'Barcelona', 'Munich', 'Oslo', 'Frankfurt', 'Split'],
        'Oslo': ['Split', 'Reykjavik', 'Bucharest', 'Frankfurt', 'Munich', 'Stockholm', 'Barcelona'],
        'Split': ['Oslo', 'Stockholm', 'Barcelona', 'Frankfurt', 'Munich']
    }
    
    # 5. Transition constraints - can only move between connected cities
    for day in range(1, days):
        for from_city in cities:
            from_idx = city_indices[from_city]
            for to_city in cities:
                to_idx = city_indices[to_city]
                if to_city not in connections[from_city] and from_city != to_city:
                    s.add(Implies(And(city_day[from_idx][day-1], city_day[to_idx][day]),
                          False))
    
    # 6. Stay must be consecutive days (simplified)
    for city, duration in stay_durations.items():
        idx = city_indices[city]
        # At least one sequence of 'duration' consecutive days in this city
        s.add(Or([And([city_day[idx][d] for d in range(day, day+duration)])
                for day in range(days - duration + 1)]))
    
    # Solve
    if s.check() == sat:
        m = s.model()
        # Create day-by-day itinerary
        itinerary = []
        for day in day_range:
            for i, city in enumerate(cities):
                if is_true(m.eval(city_day[i][day-1])):
                    itinerary.append((day, city))
                    break
        
        # Print itinerary
        print("20-Day European Trip Itinerary:")
        for day, city in itinerary:
            print(f"Day {day}: {city}")
        
        # Print flight transitions
        print("\nFlight Transitions:")
        prev_city = None
        for day, city in itinerary:
            if prev_city and prev_city != city:
                print(f"Day {day}: Fly from {prev_city} to {city}")
            prev_city = city
    else:
        print("No valid itinerary found")

plan_trip()