from z3 import *

def plan_trip():
    # Initialize solver
    s = Solver()

    # Cities
    cities = ['Copenhagen', 'Geneva', 'Mykonos', 'Naples', 'Prague', 
              'Dubrovnik', 'Athens', 'Santorini', 'Brussels', 'Munich']
    city_indices = {city: idx for idx, city in enumerate(cities)}
    
    # Days (1-28)
    days = 28
    day_range = range(1, days + 1)
    
    # Create variables: city_day[i][j] is True if in city i on day j
    city_day = [[Bool(f'city_{i}_day_{j}') for j in day_range] for i in range(len(cities))]
    
    # Constraints
    
    # 1. Each day must be in exactly one city
    for day in day_range:
        s.add(ExactlyOne([city_day[i][day-1] for i in range(len(cities))))
    
    # 2. Stay durations
    stay_durations = {
        'Copenhagen': 5,
        'Geneva': 3,
        'Mykonos': 2,
        'Naples': 4,
        'Prague': 2,
        'Dubrovnik': 3,
        'Athens': 4,
        'Santorini': 5,
        'Brussels': 4,
        'Munich': 5
    }
    
    for city, duration in stay_durations.items():
        idx = city_indices[city]
        # Total days in city must equal duration
        s.add(Sum([If(city_day[idx][day-1], 1, 0) for day in day_range]) == duration)
    
    # 3. Fixed events
    # Friend in Copenhagen between day 11-15
    copenhagen_idx = city_indices['Copenhagen']
    s.add(Or([city_day[copenhagen_idx][d] for d in range(10, 15)]))
    
    # Conference in Mykonos between day 27-28
    mykonos_idx = city_indices['Mykonos']
    s.add(And(city_day[mykonos_idx][26], city_day[mykonos_idx][27]))
    
    # Relatives in Naples between day 5-8
    naples_idx = city_indices['Naples']
    s.add(Or([city_day[naples_idx][d] for d in range(4, 8)]))
    
    # Workshop in Athens between day 8-11
    athens_idx = city_indices['Athens']
    s.add(Or([city_day[athens_idx][d] for d in range(7, 11)]))
    
    # 4. Flight connections (direct flights)
    connections = {
        'Copenhagen': ['Dubrovnik', 'Brussels', 'Naples', 'Athens', 'Geneva', 'Santorini', 'Munich'],
        'Geneva': ['Prague', 'Athens', 'Mykonos', 'Naples', 'Santorini', 'Dubrovnik', 'Brussels', 'Munich'],
        'Mykonos': ['Geneva', 'Naples', 'Munich', 'Athens'],
        'Naples': ['Dubrovnik', 'Mykonos', 'Copenhagen', 'Athens', 'Munich', 'Geneva', 'Santorini'],
        'Prague': ['Geneva', 'Athens', 'Brussels', 'Munich', 'Copenhagen'],
        'Dubrovnik': ['Copenhagen', 'Naples', 'Athens', 'Geneva', 'Munich'],
        'Athens': ['Geneva', 'Dubrovnik', 'Santorini', 'Naples', 'Mykonos', 'Prague', 'Brussels', 'Munich', 'Copenhagen'],
        'Santorini': ['Geneva', 'Athens', 'Copenhagen', 'Naples'],
        'Brussels': ['Copenhagen', 'Naples', 'Prague', 'Athens', 'Munich', 'Geneva'],
        'Munich': ['Mykonos', 'Naples', 'Dubrovnik', 'Brussels', 'Athens', 'Geneva', 'Copenhagen', 'Prague']
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
        print("28-Day European Trip Itinerary:")
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