from z3 import *

def plan_trip():
    # Initialize solver
    s = Solver()

    # Cities
    cities = ['Oslo', 'Stuttgart', 'Venice', 'Split', 'Barcelona', 
              'Brussels', 'Copenhagen']
    city_indices = {city: idx for idx, city in enumerate(cities)}
    
    # Days (1-16)
    days = 16
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
        'Stuttgart': 3,
        'Venice': 4,
        'Split': 4,
        'Barcelona': 3,
        'Brussels': 3,
        'Copenhagen': 3
    }
    
    for city, duration in stay_durations.items():
        idx = city_indices[city]
        # Total days in city must equal duration
        s.add(Sum([If(city_day[idx][day-1], 1, 0) for day in day_range]) == duration)
    
    # 3. Fixed events
    # Friends in Oslo between day 3-4
    oslo_idx = city_indices['Oslo']
    s.add(Or(city_day[oslo_idx][2], city_day[oslo_idx][3]))  # Days 3-4
    
    # Annual show in Barcelona between day 1-3
    barcelona_idx = city_indices['Barcelona']
    s.add(And([city_day[barcelona_idx][d] for d in range(3)]))  # Days 1-3
    
    # Friend in Brussels between day 9-11
    brussels_idx = city_indices['Brussels']
    s.add(Or([city_day[brussels_idx][d] for d in range(8, 11)]))  # Days 9-11
    
    # 4. Flight connections (direct flights)
    connections = {
        'Venice': ['Stuttgart', 'Barcelona', 'Brussels', 'Oslo', 'Copenhagen'],
        'Oslo': ['Brussels', 'Split', 'Venice', 'Copenhagen', 'Barcelona'],
        'Split': ['Copenhagen', 'Oslo', 'Barcelona', 'Stuttgart'],
        'Barcelona': ['Copenhagen', 'Venice', 'Stuttgart', 'Split', 'Oslo', 'Brussels'],
        'Brussels': ['Oslo', 'Venice', 'Copenhagen'],
        'Copenhagen': ['Split', 'Barcelona', 'Brussels', 'Oslo', 'Venice', 'Stuttgart'],
        'Stuttgart': ['Venice', 'Barcelona', 'Copenhagen', 'Split']
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
        print("16-Day European Trip Itinerary:")
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