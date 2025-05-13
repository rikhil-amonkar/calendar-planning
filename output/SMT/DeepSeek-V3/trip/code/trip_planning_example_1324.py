from z3 import *

def plan_trip():
    # Initialize solver
    s = Solver()

    # Cities
    cities = ['Venice', 'Barcelona', 'Copenhagen', 'Lyon', 'Reykjavik',
              'Dubrovnik', 'Athens', 'Tallinn', 'Munich']
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
        'Venice': 4,
        'Barcelona': 3,
        'Copenhagen': 4,
        'Lyon': 4,
        'Reykjavik': 4,
        'Dubrovnik': 5,
        'Athens': 2,
        'Tallinn': 5,
        'Munich': 3
    }
    
    for city, duration in stay_durations.items():
        idx = city_indices[city]
        # Total days in city must equal duration
        s.add(Sum([If(city_day[idx][day-1], 1, 0) for day in day_range]) == duration)
    
    # 3. Fixed events
    # Friend in Barcelona between day 10-12
    barcelona_idx = city_indices['Barcelona']
    s.add(Or([city_day[barcelona_idx][d] for d in range(9, 12)]))  # Days 10-12
    
    # Relatives in Copenhagen between day 7-10
    copenhagen_idx = city_indices['Copenhagen']
    s.add(Or([city_day[copenhagen_idx][d] for d in range(6, 10)]))  # Days 7-10
    
    # Wedding in Dubrovnik between day 16-20
    dubrovnik_idx = city_indices['Dubrovnik']
    s.add(Or([city_day[dubrovnik_idx][d] for d in range(15, 20)]))  # Days 16-20
    
    # 4. Flight connections (direct flights)
    connections = {
        'Copenhagen': ['Athens', 'Dubrovnik', 'Munich', 'Reykjavik', 'Venice', 'Barcelona', 'Tallinn'],
        'Munich': ['Tallinn', 'Copenhagen', 'Venice', 'Reykjavik', 'Athens', 'Lyon', 'Dubrovnik', 'Barcelona'],
        'Venice': ['Munich', 'Athens', 'Lyon', 'Barcelona', 'Copenhagen'],
        'Reykjavik': ['Athens', 'Copenhagen', 'Munich', 'Barcelona'],
        'Athens': ['Copenhagen', 'Dubrovnik', 'Venice', 'Reykjavik', 'Munich', 'Barcelona'],
        'Lyon': ['Barcelona', 'Munich', 'Venice'],
        'Barcelona': ['Lyon', 'Dubrovnik', 'Reykjavik', 'Athens', 'Copenhagen', 'Venice', 'Munich', 'Tallinn'],
        'Dubrovnik': ['Copenhagen', 'Athens', 'Barcelona', 'Munich'],
        'Tallinn': ['Munich', 'Copenhagen', 'Barcelona']
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