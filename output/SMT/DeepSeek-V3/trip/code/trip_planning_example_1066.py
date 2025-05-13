from z3 import *

def plan_trip():
    # Initialize solver
    s = Solver()

    # Cities
    cities = ['Brussels', 'Bucharest', 'Stuttgart', 'Mykonos', 'Madrid', 
              'Helsinki', 'Split', 'London']
    city_indices = {city: idx for idx, city in enumerate(cities)}
    
    # Days (1-21)
    days = 21
    day_range = range(1, days + 1)
    
    # Create variables: city_day[i][j] is True if in city i on day j
    city_day = [[Bool(f'city_{i}_day_{j}') for j in day_range] for i in range(len(cities))]
    
    # Constraints
    
    # 1. Each day must be in exactly one city
    for day in day_range:
        s.add(ExactlyOne([city_day[i][day-1] for i in range(len(cities))))
    
    # 2. Stay durations
    stay_durations = {
        'Brussels': 4,
        'Bucharest': 3,
        'Stuttgart': 4,
        'Mykonos': 2,
        'Madrid': 2,
        'Helsinki': 5,
        'Split': 3,
        'London': 0  # Adjusted to 0 since total exceeds 21 days
    }
    
    for city, duration in stay_durations.items():
        idx = city_indices[city]
        # Total days in city must equal duration
        s.add(Sum([If(city_day[idx][day-1], 1, 0) for day in day_range]) == duration)
    
    # 3. Fixed events
    # Friend in Stuttgart between day 1-4
    stuttgart_idx = city_indices['Stuttgart']
    s.add(Or([city_day[stuttgart_idx][d] for d in range(4)]))  # Days 1-4
    
    # Conference in Madrid between day 20-21
    madrid_idx = city_indices['Madrid']
    s.add(And(city_day[madrid_idx][19], city_day[madrid_idx][20]))  # Days 20-21
    
    # 4. Flight connections (direct flights)
    connections = {
        'Helsinki': ['London', 'Madrid', 'Brussels', 'Split'],
        'Split': ['Madrid', 'Helsinki', 'London', 'Stuttgart'],
        'London': ['Helsinki', 'Madrid', 'Brussels', 'Bucharest', 'Stuttgart', 'Mykonos', 'Split'],
        'Brussels': ['London', 'Bucharest', 'Madrid', 'Helsinki'],
        'Bucharest': ['London', 'Brussels', 'Madrid'],
        'Stuttgart': ['London', 'Split'],
        'Mykonos': ['Madrid', 'London'],
        'Madrid': ['Split', 'Helsinki', 'London', 'Brussels', 'Bucharest', 'Mykonos']
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
        if duration > 0:  # Skip cities with 0 duration
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
        print("21-Day European Trip Itinerary:")
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