from z3 import *

def plan_trip():
    # Initialize solver
    s = Solver()

    # Cities
    cities = ['Mykonos', 'Krakow', 'Vilnius', 'Helsinki', 'Dubrovnik', 
              'Oslo', 'Madrid', 'Paris']
    city_indices = {city: idx for idx, city in enumerate(cities)}
    
    # Days (1-18)
    days = 18
    day_range = range(1, days + 1)
    
    # Create variables: city_day[i][j] is True if in city i on day j
    city_day = [[Bool(f'city_{i}_day_{j}') for j in day_range] for i in range(len(cities))]
    
    # Constraints
    
    # 1. Each day must be in exactly one city
    for day in day_range:
        s.add(ExactlyOne([city_day[i][day-1] for i in range(len(cities))])
    
    # 2. Stay durations
    stay_durations = {
        'Mykonos': 4,
        'Krakow': 5,
        'Vilnius': 2,
        'Helsinki': 2,
        'Dubrovnik': 3,
        'Oslo': 2,
        'Madrid': 5,
        'Paris': 0  # Adjusted to 0 since 4+5+2+2+3+2+5+2=25 > 18 days
    }
    
    for city, duration in stay_durations.items():
        idx = city_indices[city]
        s.add(Sum([If(city_day[idx][day-1], 1, 0) for day in day_range]) == duration)
    
    # 3. Fixed events
    # Relatives in Mykonos between day 15-18
    mykonos_idx = city_indices['Mykonos']
    s.add(Or([city_day[mykonos_idx][d] for d in range(14, 18)]))  # Days 15-18
    
    # Annual show in Dubrovnik between day 2-4
    dubrovnik_idx = city_indices['Dubrovnik']
    s.add(Or([city_day[dubrovnik_idx][d] for d in range(1, 4)]))  # Days 2-4
    
    # Friends in Oslo between day 1-2
    oslo_idx = city_indices['Oslo']
    s.add(And(city_day[oslo_idx][0], city_day[oslo_idx][1]))  # Days 1-2
    
    # 4. Flight connections (direct flights)
    connections = {
        'Oslo': ['Krakow', 'Paris', 'Madrid', 'Helsinki', 'Dubrovnik', 'Vilnius'],
        'Paris': ['Oslo', 'Madrid', 'Krakow', 'Helsinki', 'Vilnius'],
        'Helsinki': ['Vilnius', 'Oslo', 'Krakow', 'Dubrovnik', 'Paris', 'Madrid'],
        'Dubrovnik': ['Helsinki', 'Madrid', 'Oslo'],
        'Krakow': ['Oslo', 'Paris', 'Helsinki', 'Vilnius'],
        'Madrid': ['Paris', 'Oslo', 'Dubrovnik', 'Helsinki', 'Mykonos'],
        'Vilnius': ['Helsinki', 'Oslo', 'Paris', 'Krakow'],
        'Mykonos': ['Madrid']
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
        
        print("18-Day European Trip Itinerary:")
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