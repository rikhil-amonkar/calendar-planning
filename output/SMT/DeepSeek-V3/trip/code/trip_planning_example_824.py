from z3 import *

def plan_trip():
    # Initialize solver
    s = Solver()

    # Cities
    cities = ['Berlin', 'Split', 'Bucharest', 'Riga', 'Lisbon', 'Tallinn', 'Lyon']
    city_indices = {city: idx for idx, city in enumerate(cities)}
    
    # Days (1-22)
    days = 22
    day_range = range(1, days + 1)
    
    # Create variables: city_day[i][j] is True if in city i on day j
    city_day = [[Bool(f'city_{i}_day_{j}') for j in day_range] for i in range(len(cities))]
    
    # Constraints
    
    # 1. Each day must be in exactly one city
    for day in day_range:
        s.add(ExactlyOne([city_day[i][day-1] for i in range(len(cities))])
    
    # 2. Stay durations
    stay_durations = {
        'Berlin': 5,
        'Split': 3,
        'Bucharest': 3,
        'Riga': 5,
        'Lisbon': 3,
        'Tallinn': 4,
        'Lyon': 5
    }
    
    for city, duration in stay_durations.items():
        idx = city_indices[city]
        # Total days in city must equal duration
        s.add(Sum([If(city_day[idx][day-1], 1, 0) for day in day_range]) == duration)
    
    # 3. Fixed events
    # Annual show in Berlin between day 1-5
    berlin_idx = city_indices['Berlin']
    s.add(And([city_day[berlin_idx][d] for d in range(5)]))  # Days 1-5
    
    # Relatives in Bucharest between day 13-15
    bucharest_idx = city_indices['Bucharest']
    s.add(Or([city_day[bucharest_idx][d] for d in range(12, 15)]))  # Days 13-15
    
    # Wedding in Lyon between day 7-11
    lyon_idx = city_indices['Lyon']
    s.add(Or([city_day[lyon_idx][d] for d in range(6, 11)]))  # Days 7-11
    
    # 4. Flight connections (direct flights)
    connections = {
        'Berlin': ['Lisbon', 'Riga', 'Split', 'Tallinn'],
        'Split': ['Berlin', 'Lyon'],
        'Bucharest': ['Lisbon', 'Riga', 'Lyon'],
        'Riga': ['Bucharest', 'Berlin', 'Lisbon', 'Tallinn'],
        'Lisbon': ['Bucharest', 'Berlin', 'Riga', 'Lyon'],
        'Tallinn': ['Riga', 'Berlin'],
        'Lyon': ['Split', 'Lisbon', 'Bucharest']
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
        print("22-Day European Trip Itinerary:")
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