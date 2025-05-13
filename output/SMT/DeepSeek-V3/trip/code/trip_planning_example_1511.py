from z3 import *

def plan_trip():
    # Initialize solver
    s = Solver()

    # Cities
    cities = ['Venice', 'Reykjavik', 'Munich', 'Santorini', 'Manchester', 
              'Porto', 'Bucharest', 'Tallinn', 'Valencia', 'Vienna']
    city_indices = {city: idx for idx, city in enumerate(cities)}
    
    # Days (1-24)
    days = 24
    day_range = range(1, days + 1)
    
    # Create variables: city_day[i][j] is True if in city i on day j
    city_day = [[Bool(f'city_{i}_day_{j}') for j in day_range] for i in range(len(cities))]
    
    # Constraints
    
    # 1. Each day must be in exactly one city
    for day in day_range:
        s.add(ExactlyOne([city_day[i][day-1] for i in range(len(cities))))
    
    # 2. Stay durations
    stay_durations = {
        'Venice': 3,
        'Reykjavik': 2,
        'Munich': 3,
        'Santorini': 3,
        'Manchester': 3,
        'Porto': 3,
        'Bucharest': 5,
        'Tallinn': 4,
        'Valencia': 2,
        'Vienna': 5
    }
    
    for city, duration in stay_durations.items():
        idx = city_indices[city]
        # Total days in city must equal duration
        s.add(Sum([If(city_day[idx][day-1], 1, 0) for day in day_range]) == duration)
    
    # 3. Fixed events
    # Annual show in Munich between day 4-6
    munich_idx = city_indices['Munich']
    s.add(And([city_day[munich_idx][d] for d in range(3, 6)]))  # Days 4-6
    
    # Relatives in Santorini between day 8-10
    santorini_idx = city_indices['Santorini']
    s.add(Or([city_day[santorini_idx][d] for d in range(7, 10)]))  # Days 8-10
    
    # Workshop in Valencia between day 14-15
    valencia_idx = city_indices['Valencia']
    s.add(Or(city_day[valencia_idx][13], city_day[valencia_idx][14]))  # Days 14-15
    
    # 4. Flight connections (direct flights)
    connections = {
        'Bucharest': ['Manchester', 'Valencia', 'Vienna', 'Munich', 'Santorini'],
        'Munich': ['Venice', 'Porto', 'Manchester', 'Reykjavik', 'Vienna', 'Bucharest', 'Valencia', 'Tallinn'],
        'Santorini': ['Manchester', 'Venice', 'Vienna', 'Bucharest'],
        'Vienna': ['Reykjavik', 'Valencia', 'Manchester', 'Porto', 'Venice', 'Bucharest', 'Santorini', 'Munich'],
        'Venice': ['Munich', 'Santorini', 'Manchester', 'Vienna'],
        'Manchester': ['Bucharest', 'Santorini', 'Porto', 'Venice', 'Vienna', 'Munich'],
        'Porto': ['Munich', 'Vienna', 'Manchester', 'Valencia'],
        'Tallinn': ['Munich'],
        'Valencia': ['Vienna', 'Bucharest', 'Porto', 'Munich'],
        'Reykjavik': ['Vienna', 'Munich']
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
        print("24-Day European Trip Itinerary:")
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