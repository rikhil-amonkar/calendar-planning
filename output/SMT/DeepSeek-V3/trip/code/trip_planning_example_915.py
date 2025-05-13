from z3 import *

def plan_trip():
    # Initialize solver
    s = Solver()

    # Cities
    cities = ['Bucharest', 'Venice', 'Prague', 'Frankfurt', 'Zurich', 'Florence', 'Tallinn']
    city_indices = {city: idx for idx, city in enumerate(cities)}
    
    # Days (1-26)
    days = 26
    day_range = range(1, days + 1)
    
    # Create variables: city_day[i][j] is True if in city i on day j
    city_day = [[Bool(f'city_{i}_day_{j}') for j in day_range] for i in range(len(cities))]
    
    # Constraints
    
    # 1. Each day must be in exactly one city
    for day in day_range:
        s.add(ExactlyOne([city_day[i][day-1] for i in range(len(cities))))
    
    # 2. Stay durations
    stay_durations = {
        'Bucharest': 3,
        'Venice': 5,
        'Prague': 4,
        'Frankfurt': 5,
        'Zurich': 5,
        'Florence': 5,
        'Tallinn': 5
    }
    
    for city, duration in stay_durations.items():
        idx = city_indices[city]
        # Total days in city must equal duration
        s.add(Sum([If(city_day[idx][day-1], 1, 0) for day in day_range]) == duration)
    
    # 3. Fixed events
    # Wedding in Venice between day 22-26
    venice_idx = city_indices['Venice']
    s.add(And([city_day[venice_idx][d] for d in range(21, 26)]))  # Days 22-26
    
    # Annual show in Frankfurt between day 12-16
    frankfurt_idx = city_indices['Frankfurt']
    s.add(Or([city_day[frankfurt_idx][d] for d in range(11, 16)]))  # Days 12-16
    
    # Friends in Tallinn between day 8-12
    tallinn_idx = city_indices['Tallinn']
    s.add(Or([city_day[tallinn_idx][d] for d in range(7, 12)]))  # Days 8-12
    
    # 4. Flight connections (direct flights)
    connections = {
        'Prague': ['Tallinn', 'Zurich', 'Florence', 'Bucharest', 'Frankfurt'],
        'Frankfurt': ['Bucharest', 'Venice', 'Tallinn', 'Zurich', 'Florence', 'Prague'],
        'Bucharest': ['Frankfurt', 'Prague', 'Zurich'],
        'Zurich': ['Prague', 'Florence', 'Frankfurt', 'Venice', 'Bucharest', 'Tallinn'],
        'Florence': ['Prague', 'Frankfurt', 'Zurich'],
        'Tallinn': ['Prague', 'Frankfurt', 'Zurich'],
        'Venice': ['Frankfurt', 'Zurich']
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
        print("26-Day European Trip Itinerary:")
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