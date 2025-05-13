from z3 import *

def plan_trip():
    # Initialize solver
    s = Solver()

    # Cities
    cities = ['Vienna', 'Lyon', 'Edinburgh', 'Reykjavik', 'Stuttgart', 'Manchester', 'Split', 'Prague']
    city_indices = {city: idx for idx, city in enumerate(cities)}
    
    # Days (1-25)
    days = 25
    day_range = range(1, days + 1)
    
    # Create variables: city_day[i][j] is True if in city i on day j
    city_day = [[Bool(f'city_{i}_day_{j}') for j in day_range] for i in range(len(cities))]
    
    # Constraints
    
    # 1. Each day must be in exactly one city
    for day in day_range:
        s.add(ExactlyOne([city_day[i][day-1] for i in range(len(cities))]))
    
    # 2. Stay durations
    stay_durations = {
        'Vienna': 4,
        'Lyon': 3,
        'Edinburgh': 4,
        'Reykjavik': 5,
        'Stuttgart': 5,
        'Manchester': 2,
        'Split': 5,
        'Prague': 4
    }
    
    for city, duration in stay_durations.items():
        idx = city_indices[city]
        # Total days in city must equal duration
        s.add(Sum([If(city_day[idx][day-1], 1, 0) for day in day_range]) == duration)
    
    # 3. Fixed events
    # Annual show in Edinburgh between day 5-8
    edinburgh_idx = city_indices['Edinburgh']
    s.add(And([city_day[edinburgh_idx][d] for d in range(4, 8)]))  # Days 5-8
    
    # Wedding in Split between day 19-23
    split_idx = city_indices['Split']
    s.add(Or([city_day[split_idx][d] for d in range(18, 23)]))  # Days 19-23
    
    # 4. Flight connections (direct flights)
    connections = {
        'Reykjavik': ['Stuttgart', 'Vienna', 'Prague'],
        'Stuttgart': ['Split', 'Vienna', 'Edinburgh', 'Manchester', 'Reykjavik'],
        'Prague': ['Manchester', 'Edinburgh', 'Vienna', 'Split', 'Lyon', 'Reykjavik'],
        'Edinburgh': ['Prague', 'Stuttgart'],
        'Manchester': ['Split', 'Prague', 'Vienna', 'Stuttgart'],
        'Split': ['Stuttgart', 'Lyon', 'Manchester', 'Prague', 'Vienna'],
        'Vienna': ['Lyon', 'Manchester', 'Split', 'Stuttgart', 'Reykjavik', 'Prague'],
        'Lyon': ['Vienna', 'Split', 'Prague']
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
        print("25-Day European Trip Itinerary:")
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