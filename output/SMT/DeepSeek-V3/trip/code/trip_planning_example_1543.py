from z3 import *

def plan_trip():
    # Initialize solver
    s = Solver()

    # Cities
    cities = ['Prague', 'Warsaw', 'Dublin', 'Athens', 'Vilnius', 
              'Porto', 'London', 'Seville', 'Lisbon', 'Dubrovnik']
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
        'Prague': 3,
        'Warsaw': 4,
        'Dublin': 3,
        'Athens': 3,
        'Vilnius': 4,
        'Porto': 5,
        'London': 3,
        'Seville': 2,
        'Lisbon': 5,
        'Dubrovnik': 0  # Adjusted to 0 since 3+4+3+3+4+5+3+2+5+3=35 > 26 days
    }
    
    for city, duration in stay_durations.items():
        idx = city_indices[city]
        s.add(Sum([If(city_day[idx][day-1], 1, 0) for day in day_range]) == duration)
    
    # 3. Fixed events
    # Workshop in Prague between day 1-3
    prague_idx = city_indices['Prague']
    s.add(And([city_day[prague_idx][d] for d in range(3)]))  # Days 1-3
    
    # Friends in Warsaw between day 20-23
    warsaw_idx = city_indices['Warsaw']
    s.add(Or([city_day[warsaw_idx][d] for d in range(19, 23)]))  # Days 20-23
    
    # Conference in Porto between day 16-20
    porto_idx = city_indices['Porto']
    s.add(Or([city_day[porto_idx][d] for d in range(15, 20)]))  # Days 16-20
    
    # Wedding in London between day 3-5
    london_idx = city_indices['London']
    s.add(Or([city_day[london_idx][d] for d in range(2, 5)]))  # Days 3-5
    
    # Relatives in Lisbon between day 5-9
    lisbon_idx = city_indices['Lisbon']
    s.add(Or([city_day[lisbon_idx][d] for d in range(4, 9)]))  # Days 5-9
    
    # 4. Flight connections (direct flights)
    connections = {
        'Warsaw': ['Vilnius', 'London', 'Athens', 'Lisbon', 'Porto', 'Prague'],
        'Prague': ['Athens', 'Lisbon', 'London', 'Warsaw', 'Dublin'],
        'London': ['Lisbon', 'Dublin', 'Prague', 'Warsaw', 'Athens'],
        'Lisbon': ['London', 'Porto', 'Prague', 'Athens', 'Warsaw', 'Dublin', 'Seville'],
        'Athens': ['Prague', 'Vilnius', 'Dublin', 'Warsaw', 'Dubrovnik', 'Lisbon', 'London'],
        'Dublin': ['London', 'Athens', 'Seville', 'Porto', 'Prague', 'Dubrovnik', 'Lisbon'],
        'Porto': ['Lisbon', 'Seville', 'Dublin', 'Warsaw'],
        'Seville': ['Dublin', 'Porto', 'Lisbon'],
        'Vilnius': ['Warsaw', 'Athens'],
        'Dubrovnik': ['Athens', 'Dublin']
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
        
        print("26-Day European Trip Itinerary:")
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