from z3 import *

def plan_trip():
    # Initialize solver
    s = Solver()

    # Cities
    cities = ['Oslo', 'Helsinki', 'Edinburgh', 'Riga', 'Tallinn', 
              'Budapest', 'Vilnius', 'Porto', 'Geneva']
    city_indices = {city: idx for idx, city in enumerate(cities)}
    
    # Days (1-25)
    days = 25
    day_range = range(1, days + 1)
    
    # Create variables: city_day[i][j] is True if in city i on day j
    city_day = [[Bool(f'city_{i}_day_{j}') for j in day_range] for i in range(len(cities))]
    
    # Constraints
    
    # 1. Each day must be in exactly one city
    for day in day_range:
        s.add(ExactlyOne([city_day[i][day-1] for i in range(len(cities))])
    
    # 2. Stay durations
    stay_durations = {
        'Oslo': 2,
        'Helsinki': 2,
        'Edinburgh': 3,
        'Riga': 2,
        'Tallinn': 5,
        'Budapest': 5,
        'Vilnius': 5,
        'Porto': 5,
        'Geneva': 4
    }
    
    for city, duration in stay_durations.items():
        idx = city_indices[city]
        s.add(Sum([If(city_day[idx][day-1], 1, 0) for day in day_range]) == duration)
    
    # 3. Fixed events
    # Friend in Oslo between day 24-25
    oslo_idx = city_indices['Oslo']
    s.add(And(city_day[oslo_idx][23], city_day[oslo_idx][24]))  # Days 24-25
    
    # Wedding in Tallinn between day 4-8
    tallinn_idx = city_indices['Tallinn']
    s.add(Or([city_day[tallinn_idx][d] for d in range(3, 8)]))  # Days 4-8
    
    # 4. Flight connections (direct flights)
    connections = {
        'Oslo': ['Porto', 'Riga', 'Geneva', 'Edinburgh', 'Vilnius', 'Budapest', 'Helsinki', 'Tallinn'],
        'Helsinki': ['Vilnius', 'Edinburgh', 'Oslo', 'Tallinn', 'Budapest', 'Geneva', 'Riga'],
        'Edinburgh': ['Budapest', 'Geneva', 'Porto', 'Oslo', 'Helsinki', 'Riga'],
        'Riga': ['Tallinn', 'Oslo', 'Helsinki', 'Vilnius'],
        'Tallinn': ['Vilnius', 'Helsinki', 'Oslo', 'Riga'],
        'Budapest': ['Edinburgh', 'Geneva', 'Helsinki', 'Oslo'],
        'Vilnius': ['Helsinki', 'Tallinn', 'Oslo', 'Riga'],
        'Porto': ['Oslo', 'Geneva', 'Edinburgh'],
        'Geneva': ['Oslo', 'Budapest', 'Edinburgh', 'Helsinki', 'Porto']
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
        
        print("25-Day European Trip Itinerary:")
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