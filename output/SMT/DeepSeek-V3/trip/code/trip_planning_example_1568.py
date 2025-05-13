from z3 import *

def plan_trip():
    # Initialize solver
    s = Solver()

    # Cities
    cities = ['Prague', 'Brussels', 'Riga', 'Munich', 'Seville', 
              'Stockholm', 'Istanbul', 'Amsterdam', 'Vienna', 'Split']
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
        'Prague': 5,
        'Brussels': 2,
        'Riga': 2,
        'Munich': 2,
        'Seville': 3,
        'Stockholm': 2,
        'Istanbul': 2,
        'Amsterdam': 3,
        'Vienna': 5,
        'Split': 3
    }
    
    for city, duration in stay_durations.items():
        idx = city_indices[city]
        # Total days in city must equal duration
        s.add(Sum([If(city_day[idx][day-1], 1, 0) for day in day_range]) == duration)
    
    # 3. Fixed events
    # Annual show in Prague between day 5-9
    prague_idx = city_indices['Prague']
    s.add(Or([city_day[prague_idx][d] for d in range(4, 9)]))  # Days 5-9
    
    # Friends in Riga between day 15-16
    riga_idx = city_indices['Riga']
    s.add(Or(city_day[riga_idx][14], city_day[riga_idx][15]))  # Days 15-16
    
    # Conference in Stockholm between day 16-17
    stockholm_idx = city_indices['Stockholm']
    s.add(Or(city_day[stockholm_idx][15], city_day[stockholm_idx][16]))  # Days 16-17
    
    # Friend in Vienna between day 1-5
    vienna_idx = city_indices['Vienna']
    s.add(Or([city_day[vienna_idx][d] for d in range(5)]))  # Days 1-5
    
    # Relatives in Split between day 11-13
    split_idx = city_indices['Split']
    s.add(Or([city_day[split_idx][d] for d in range(10, 13)]))  # Days 11-13
    
    # 4. Flight connections (direct flights)
    connections = {
        'Prague': ['Split', 'Munich', 'Amsterdam', 'Brussels', 'Istanbul', 'Stockholm', 'Riga', 'Vienna'],
        'Brussels': ['Stockholm', 'Vienna', 'Riga', 'Munich', 'Seville', 'Istanbul', 'Prague'],
        'Riga': ['Stockholm', 'Istanbul', 'Amsterdam', 'Munich', 'Brussels', 'Prague', 'Vienna'],
        'Munich': ['Istanbul', 'Amsterdam', 'Brussels', 'Prague', 'Split', 'Stockholm', 'Seville', 'Vienna'],
        'Seville': ['Vienna', 'Brussels', 'Amsterdam', 'Munich'],
        'Stockholm': ['Riga', 'Brussels', 'Split', 'Amsterdam', 'Vienna', 'Istanbul', 'Munich', 'Prague'],
        'Istanbul': ['Munich', 'Riga', 'Amsterdam', 'Stockholm', 'Brussels', 'Prague', 'Vienna'],
        'Amsterdam': ['Munich', 'Split', 'Stockholm', 'Riga', 'Prague', 'Seville', 'Vienna', 'Istanbul'],
        'Vienna': ['Brussels', 'Riga', 'Stockholm', 'Istanbul', 'Seville', 'Split', 'Amsterdam', 'Munich', 'Prague'],
        'Split': ['Prague', 'Stockholm', 'Amsterdam', 'Munich', 'Vienna']
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