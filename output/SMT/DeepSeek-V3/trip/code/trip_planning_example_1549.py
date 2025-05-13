from z3 import *

def plan_trip():
    # Initialize solver
    s = Solver()

    # Cities
    cities = ['Prague', 'Tallinn', 'Warsaw', 'Porto', 'Naples', 'Milan', 
              'Lisbon', 'Santorini', 'Riga', 'Stockholm']
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
        'Prague': 5,
        'Tallinn': 3,
        'Warsaw': 2,
        'Porto': 3,
        'Naples': 5,
        'Milan': 3,
        'Lisbon': 5,
        'Santorini': 5,
        'Riga': 4,
        'Stockholm': 2
    }
    
    for city, duration in stay_durations.items():
        idx = city_indices[city]
        s.add(Sum([If(city_day[idx][day-1], 1, 0) for day in day_range]) == duration)
    
    # 3. Fixed events
    # Relatives in Tallinn between day 18-20
    tallinn_idx = city_indices['Tallinn']
    s.add(And([city_day[tallinn_idx][d] for d in range(17, 20)]))  # Days 18-20
    
    # Friend in Milan between day 24-26
    milan_idx = city_indices['Milan']
    s.add(Or([city_day[milan_idx][d] for d in range(23, 26)]))  # Days 24-26
    
    # Annual show in Riga between day 5-8
    riga_idx = city_indices['Riga']
    s.add(And([city_day[riga_idx][d] for d in range(4, 8)]))  # Days 5-8
    
    # 4. Flight connections (direct flights)
    connections = {
        'Riga': ['Prague', 'Milan', 'Tallinn', 'Warsaw', 'Stockholm', 'Lisbon'],
        'Stockholm': ['Milan', 'Lisbon', 'Santorini', 'Tallinn', 'Prague', 'Warsaw'],
        'Naples': ['Warsaw', 'Milan', 'Lisbon', 'Santorini'],
        'Lisbon': ['Stockholm', 'Warsaw', 'Naples', 'Porto', 'Prague', 'Milan', 'Riga'],
        'Tallinn': ['Prague', 'Warsaw', 'Stockholm', 'Riga'],
        'Warsaw': ['Naples', 'Lisbon', 'Porto', 'Riga', 'Stockholm', 'Milan', 'Prague', 'Tallinn'],
        'Milan': ['Stockholm', 'Riga', 'Naples', 'Porto', 'Prague', 'Lisbon', 'Santorini', 'Warsaw'],
        'Porto': ['Lisbon', 'Milan', 'Warsaw'],
        'Prague': ['Riga', 'Tallinn', 'Stockholm', 'Lisbon', 'Milan', 'Warsaw'],
        'Santorini': ['Stockholm', 'Naples', 'Milan']
    }
    
    # 5. Transition constraints
    for day in range(1, days):
        for from_city in cities:
            from_idx = city_indices[from_city]
            for to_city in cities:
                to_idx = city_indices[to_city]
                if to_city not in connections[from_city] and from_city != to_city:
                    s.add(Implies(And(city_day[from_idx][day-1], city_day[to_idx][day]),
                          False))
    
    # 6. Consecutive stays
    for city, duration in stay_durations.items():
        if duration > 0:
            idx = city_indices[city]
            s.add(Or([And([city_day[idx][d] for d in range(day, day+duration)])
                    for day in range(days - duration + 1)]))
    
    # Solve
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for day in day_range:
            for i, city in enumerate(cities):
                if is_true(m.eval(city_day[i][day-1])):
                    itinerary.append((day, city))
                    break
        
        print("28-Day European Trip Itinerary:")
        for day, city in itinerary:
            print(f"Day {day}: {city}")
        
        print("\nFlight Transitions:")
        prev_city = None
        for day, city in itinerary:
            if prev_city and prev_city != city:
                print(f"Day {day}: Fly from {prev_city} to {city}")
            prev_city = city
    else:
        print("No valid itinerary found")

plan_trip()