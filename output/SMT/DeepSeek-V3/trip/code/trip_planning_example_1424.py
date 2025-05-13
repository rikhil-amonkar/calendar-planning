from z3 import *

def plan_trip():
    # Initialize solver
    s = Solver()

    # Cities
    cities = ['Porto', 'Amsterdam', 'Helsinki', 'Naples', 'Brussels', 'Split', 
              'Reykjavik', 'Warsaw', 'Lyon', 'Valencia']
    city_indices = {city: idx for idx, city in enumerate(cities)}
    
    # Days (1-27)
    days = 27
    day_range = range(1, days + 1)
    
    # Create variables: city_day[i][j] is True if in city i on day j
    city_day = [[Bool(f'city_{i}_day_{j}') for j in day_range] for i in range(len(cities))]
    
    # Constraints
    
    # 1. Each day must be in exactly one city
    for day in day_range:
        s.add(ExactlyOne([city_day[i][day-1] for i in range(len(cities))))
    
    # 2. Stay durations
    stay_durations = {
        'Warsaw': 3,
        'Porto': 5,
        'Naples': 4,
        'Brussels': 3,
        'Split': 3,
        'Reykjavik': 5,
        'Amsterdam': 4,
        'Lyon': 3,
        'Helsinki': 4,
        'Valencia': 2
    }
    
    for city, duration in stay_durations.items():
        idx = city_indices[city]
        # Total days in city must equal duration
        s.add(Sum([If(city_day[idx][day-1], 1, 0) for day in day_range]) == duration)
    
    # 3. Fixed events
    # Workshop in Porto between day 1-5
    porto_idx = city_indices['Porto']
    s.add(Or([city_day[porto_idx][d] for d in range(5)]))
    
    # Conference in Naples on days 17 and 20
    naples_idx = city_indices['Naples']
    s.add(city_day[naples_idx][16])  # Day 17
    s.add(city_day[naples_idx][19])  # Day 20
    
    # Annual show in Brussels from day 20-22
    brussels_idx = city_indices['Brussels']
    s.add(And(city_day[brussels_idx][19], city_day[brussels_idx][20], city_day[brussels_idx][21]))
    
    # Relatives in Amsterdam between day 5-8
    amsterdam_idx = city_indices['Amsterdam']
    s.add(Or([city_day[amsterdam_idx][d] for d in range(4, 8)]))
    
    # Wedding in Helsinki between day 8-11
    helsinki_idx = city_indices['Helsinki']
    s.add(Or([city_day[helsinki_idx][d] for d in range(7, 11)]))
    
    # 4. Flight connections (direct flights)
    connections = {
        'Amsterdam': ['Warsaw', 'Lyon', 'Naples', 'Reykjavik', 'Split', 'Helsinki', 'Valencia'],
        'Helsinki': ['Brussels', 'Warsaw', 'Split', 'Naples', 'Reykjavik'],
        'Reykjavik': ['Brussels', 'Warsaw', 'Amsterdam'],
        'Brussels': ['Helsinki', 'Lyon', 'Valencia', 'Porto', 'Naples'],
        'Porto': ['Brussels', 'Amsterdam', 'Lyon', 'Warsaw', 'Valencia'],
        'Naples': ['Valencia', 'Amsterdam', 'Split', 'Brussels', 'Warsaw', 'Helsinki'],
        'Split': ['Amsterdam', 'Lyon', 'Warsaw', 'Helsinki', 'Naples'],
        'Warsaw': ['Amsterdam', 'Helsinki', 'Split', 'Brussels', 'Naples', 'Valencia', 'Porto'],
        'Lyon': ['Amsterdam', 'Split', 'Brussels', 'Valencia', 'Porto'],
        'Valencia': ['Naples', 'Brussels', 'Lyon', 'Amsterdam', 'Porto', 'Warsaw']
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