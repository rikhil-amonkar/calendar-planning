from z3 import *

def plan_trip():
    # Initialize solver
    s = Solver()

    # Cities
    cities = ['Frankfurt', 'Manchester', 'Valencia', 'Naples', 'Oslo', 'Vilnius']
    city_indices = {city: idx for idx, city in enumerate(cities)}
    
    # Days (1-16)
    days = 16
    day_range = range(1, days + 1)
    
    # Create variables: city_day[i][j] is True if in city i on day j
    city_day = [[Bool(f'city_{i}_day_{j}') for j in day_range] for i in range(len(cities))]
    
    # Constraints
    
    # 1. Each day must be in exactly one city
    for day in day_range:
        s.add(ExactlyOne([city_day[i][day-1] for i in range(len(cities))))
    
    # 2. Stay durations
    stay_durations = {
        'Frankfurt': 4,
        'Manchester': 4,
        'Valencia': 4,
        'Naples': 4,
        'Oslo': 3,
        'Vilnius': 2
    }
    
    for city, duration in stay_durations.items():
        idx = city_indices[city]
        s.add(Sum([If(city_day[idx][day-1], 1, 0) for day in day_range]) == duration)
    
    # 3. Fixed events
    # Annual show in Frankfurt between day 13-16
    frankfurt_idx = city_indices['Frankfurt']
    s.add(And([city_day[frankfurt_idx][d] for d in range(12, 16)]))  # Days 13-16
    
    # Wedding in Vilnius between day 12-13
    vilnius_idx = city_indices['Vilnius']
    s.add(And(city_day[vilnius_idx][11], city_day[vilnius_idx][12]))  # Days 12-13
    
    # 4. Flight connections (direct flights)
    connections = {
        'Frankfurt': ['Valencia', 'Manchester', 'Naples', 'Oslo', 'Vilnius'],
        'Manchester': ['Frankfurt', 'Naples', 'Oslo'],
        'Valencia': ['Frankfurt', 'Naples'],
        'Naples': ['Frankfurt', 'Manchester', 'Oslo', 'Valencia'],
        'Oslo': ['Frankfurt', 'Naples', 'Vilnius', 'Manchester'],
        'Vilnius': ['Frankfurt', 'Oslo']
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
        
        print("16-Day European Trip Itinerary:")
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