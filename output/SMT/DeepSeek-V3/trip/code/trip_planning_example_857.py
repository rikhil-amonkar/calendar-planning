from z3 import *

def plan_trip():
    # Initialize solver
    s = Solver()

    # Cities
    cities = ['Porto', 'Geneva', 'Mykonos', 'Manchester', 'Hamburg', 
              'Naples', 'Frankfurt']
    city_indices = {city: idx for idx, city in enumerate(cities)}
    
    # Days (1-18)
    days = 18
    day_range = range(1, days + 1)
    
    # Create variables: city_day[i][j] is True if in city i on day j
    city_day = [[Bool(f'city_{i}_day_{j}') for j in day_range] for i in range(len(cities))]
    
    # Constraints
    
    # 1. Each day must be in exactly one city
    for day in day_range:
        s.add(ExactlyOne([city_day[i][day-1] for i in range(len(cities))))
    
    # 2. Stay durations
    stay_durations = {
        'Porto': 2,
        'Geneva': 3,
        'Mykonos': 3,
        'Manchester': 4,
        'Hamburg': 5,
        'Naples': 5,
        'Frankfurt': 2
    }
    
    for city, duration in stay_durations.items():
        idx = city_indices[city]
        # Total days in city must equal duration
        s.add(Sum([If(city_day[idx][day-1], 1, 0) for day in day_range]) == duration)
    
    # 3. Fixed events
    # Friend in Mykonos between day 10-12
    mykonos_idx = city_indices['Mykonos']
    s.add(Or([city_day[mykonos_idx][d] for d in range(9, 12)]))  # Days 10-12
    
    # Wedding in Manchester between day 15-18
    manchester_idx = city_indices['Manchester']
    s.add(Or([city_day[manchester_idx][d] for d in range(14, 18)]))  # Days 15-18
    
    # Annual show in Frankfurt between day 5-6
    frankfurt_idx = city_indices['Frankfurt']
    s.add(Or(city_day[frankfurt_idx][4], city_day[frankfurt_idx][5]))  # Days 5-6
    
    # 4. Flight connections (direct flights)
    connections = {
        'Hamburg': ['Frankfurt', 'Porto', 'Geneva', 'Manchester'],
        'Naples': ['Mykonos', 'Geneva', 'Frankfurt', 'Manchester'],
        'Mykonos': ['Naples', 'Geneva'],
        'Frankfurt': ['Hamburg', 'Geneva', 'Porto', 'Naples', 'Manchester'],
        'Geneva': ['Hamburg', 'Mykonos', 'Frankfurt', 'Porto', 'Manchester', 'Naples'],
        'Porto': ['Hamburg', 'Frankfurt', 'Geneva', 'Manchester'],
        'Manchester': ['Geneva', 'Naples', 'Frankfurt', 'Porto', 'Hamburg']
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
        print("18-Day European Trip Itinerary:")
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