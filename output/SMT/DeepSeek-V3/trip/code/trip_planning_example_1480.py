from z3 import *

def plan_trip():
    # Initialize solver
    s = Solver()

    # Cities
    cities = ['Istanbul', 'Vienna', 'Riga', 'Brussels', 'Madrid',
              'Vilnius', 'Venice', 'Geneva', 'Munich', 'Reykjavik']
    city_indices = {city: idx for idx, city in enumerate(cities)}
    
    # Days (1-27)
    days = 27
    day_range = range(1, days + 1)
    
    # Create variables: city_day[i][j] is True if in city i on day j
    city_day = [[Bool(f'city_{i}_day_{j}') for j in day_range] for i in range(len(cities))]
    
    # Constraints
    
    # 1. Each day must be in exactly one city
    for day in day_range:
        s.add(ExactlyOne([city_day[i][day-1] for i in range(len(cities))])
    
    # 2. Stay durations
    stay_durations = {
        'Istanbul': 4,
        'Vienna': 4,
        'Riga': 2,
        'Brussels': 2,
        'Madrid': 4,
        'Vilnius': 4,
        'Venice': 5,
        'Geneva': 4,
        'Munich': 5,
        'Reykjavik': 2
    }
    
    for city, duration in stay_durations.items():
        idx = city_indices[city]
        # Total days in city must equal duration
        s.add(Sum([If(city_day[idx][day-1], 1, 0) for day in day_range]) == duration)
    
    # 3. Fixed events
    # Wedding in Brussels between day 26-27
    brussels_idx = city_indices['Brussels']
    s.add(And(city_day[brussels_idx][25], city_day[brussels_idx][26])  # Days 26-27
    
    # Friends in Vilnius between day 20-23
    vilnius_idx = city_indices['Vilnius']
    s.add(Or([city_day[vilnius_idx][d] for d in range(19, 23)]))  # Days 20-23
    
    # Workshop in Venice between day 7-11
    venice_idx = city_indices['Venice']
    s.add(Or([city_day[venice_idx][d] for d in range(6, 11)]))  # Days 7-11
    
    # Relatives in Geneva between day 1-4
    geneva_idx = city_indices['Geneva']
    s.add(And([city_day[geneva_idx][d] for d in range(4)]))  # Days 1-4
    
    # 4. Flight connections (direct flights)
    connections = {
        'Munich': ['Vienna', 'Reykjavik', 'Madrid', 'Venice', 'Istanbul', 'Brussels'],
        'Istanbul': ['Brussels', 'Geneva', 'Vienna', 'Riga', 'Venice', 'Vilnius', 'Madrid', 'Munich'],
        'Vienna': ['Munich', 'Vilnius', 'Istanbul', 'Reykjavik', 'Venice', 'Riga', 'Madrid', 'Brussels', 'Geneva'],
        'Madrid': ['Munich', 'Venice', 'Vienna', 'Brussels', 'Istanbul', 'Geneva', 'Reykjavik'],
        'Venice': ['Brussels', 'Munich', 'Madrid', 'Vienna', 'Istanbul'],
        'Riga': ['Brussels', 'Istanbul', 'Munich', 'Vilnius', 'Vienna'],
        'Brussels': ['Istanbul', 'Venice', 'Riga', 'Vilnius', 'Reykjavik', 'Vienna', 'Geneva', 'Madrid', 'Munich'],
        'Vilnius': ['Vienna', 'Istanbul', 'Brussels', 'Munich', 'Riga'],
        'Geneva': ['Istanbul', 'Vienna', 'Madrid', 'Brussels', 'Munich'],
        'Reykjavik': ['Munich', 'Vienna', 'Brussels', 'Madrid']
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
        print("27-Day European Trip Itinerary:")
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