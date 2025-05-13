from z3 import *

def plan_trip():
    # Initialize solver
    s = Solver()

    # Cities
    cities = ['Paris', 'Florence', 'Vienna', 'Porto', 'Munich', 'Nice', 'Warsaw']
    city_indices = {city: idx for idx, city in enumerate(cities)}
    
    # Days (1-20)
    days = 20
    day_range = range(1, days + 1)
    
    # Create variables: city_day[i][j] is True if in city i on day j
    city_day = [[Bool(f'city_{i}_day_{j}') for j in day_range] for i in range(len(cities))]
    
    # Constraints
    
    # 1. Each day must be in exactly one city
    for day in day_range:
        s.add(ExactlyOne([city_day[i][day-1] for i in range(len(cities))))
    
    # 2. Stay durations
    stay_durations = {
        'Paris': 5,
        'Florence': 3,
        'Vienna': 2,
        'Porto': 3,
        'Munich': 5,
        'Nice': 5,
        'Warsaw': 3
    }
    
    for city, duration in stay_durations.items():
        idx = city_indices[city]
        s.add(Sum([If(city_day[idx][day-1], 1, 0) for day in day_range]) == duration)
    
    # 3. Fixed events
    # Relatives in Vienna between day 19-20
    vienna_idx = city_indices['Vienna']
    s.add(And(city_day[vienna_idx][18], city_day[vienna_idx][19]))  # Days 19-20
    
    # Workshop in Porto between day 1-3
    porto_idx = city_indices['Porto']
    s.add(And([city_day[porto_idx][d] for d in range(3)]))  # Days 1-3
    
    # Wedding in Warsaw between day 13-15
    warsaw_idx = city_indices['Warsaw']
    s.add(And([city_day[warsaw_idx][d] for d in range(12, 15)]))  # Days 13-15
    
    # 4. Flight connections (direct flights)
    connections = {
        'Paris': ['Florence', 'Warsaw', 'Vienna', 'Nice', 'Munich'],
        'Florence': ['Vienna', 'Munich', 'Paris'],
        'Vienna': ['Florence', 'Munich', 'Porto', 'Warsaw', 'Paris', 'Nice'],
        'Porto': ['Vienna', 'Munich', 'Nice', 'Paris', 'Warsaw'],
        'Munich': ['Vienna', 'Florence', 'Nice', 'Warsaw', 'Paris', 'Porto'],
        'Nice': ['Warsaw', 'Vienna', 'Paris', 'Porto', 'Munich'],
        'Warsaw': ['Paris', 'Vienna', 'Munich', 'Nice', 'Porto']
    }
    
    # 5. Transition constraints
    for day in range(1, days):
        for from_city in cities:
            from_idx = city_indices[from_city]
            for to_city in cities:
                to_idx = city_indices[to_city]
                if to_city not in connections[from_city] and from_city != to_city:
                    s.add(Implies(And(city_day[from_idx][day-1], city_day[to_idx][day]), False))
    
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
        
        print("20-Day European Trip Itinerary:")
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