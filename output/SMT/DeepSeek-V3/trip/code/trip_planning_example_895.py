from z3 import *

def plan_trip():
    # Initialize solver
    s = Solver()

    # Cities
    cities = ['Venice', 'London', 'Lisbon', 'Brussels', 'Reykjavik', 'Santorini', 'Madrid']
    city_indices = {city: idx for idx, city in enumerate(cities)}
    
    # Days (1-17)
    days = 17
    day_range = range(1, days + 1)
    
    # Create variables: city_day[i][j] is True if in city i on day j
    city_day = [[Bool(f'city_{i}_day_{j}') for j in day_range] for i in range(len(cities))]
    
    # Constraints
    
    # 1. Each day must be in exactly one city
    for day in day_range:
        s.add(ExactlyOne([city_day[i][day-1] for i in range(len(cities))]))
    
    # 2. Stay durations
    stay_durations = {
        'Venice': 3,
        'London': 3,
        'Lisbon': 4,
        'Brussels': 2,
        'Reykjavik': 3,
        'Santorini': 3,
        'Madrid': 5
    }
    
    for city, duration in stay_durations.items():
        idx = city_indices[city]
        s.add(Sum([If(city_day[idx][day-1], 1, 0) for day in day_range]) == duration)
    
    # 3. Fixed events
    # Relatives in Venice between day 5-7
    venice_idx = city_indices['Venice']
    s.add(And([city_day[venice_idx][d] for d in range(4, 7)]))  # Days 5-7
    
    # Conference in Brussels between day 1-2
    brussels_idx = city_indices['Brussels']
    s.add(And(city_day[brussels_idx][0], city_day[brussels_idx][1]))  # Days 1-2
    
    # Wedding in Madrid between day 7-11
    madrid_idx = city_indices['Madrid']
    s.add(Or([city_day[madrid_idx][d] for d in range(6, 11)]))  # Days 7-11
    
    # 4. Flight connections (direct flights)
    connections = {
        'Venice': ['Madrid', 'Brussels', 'Santorini', 'Lisbon', 'London'],
        'London': ['Brussels', 'Madrid', 'Santorini', 'Reykjavik', 'Lisbon', 'Venice'],
        'Lisbon': ['Reykjavik', 'Venice', 'Brussels', 'London', 'Madrid'],
        'Brussels': ['Venice', 'London', 'Lisbon', 'Reykjavik', 'Madrid'],
        'Reykjavik': ['Lisbon', 'London', 'Madrid', 'Brussels'],
        'Santorini': ['Venice', 'London', 'Madrid'],
        'Madrid': ['Venice', 'London', 'Reykjavik', 'Lisbon', 'Santorini', 'Brussels']
    }
    
    # 5. Transition constraints
    for day in range(1, days):
        for from_city in cities:
            from_idx = city_indices[from_city]
            for to_city in cities:
                to_idx = city_indices[to_city]
                if to_city not in connections[from_city] and from_city != to_city:
                    s.add(Implies(And(city_day[from_idx][day-1], city_day[to_idx][day]), False)
    
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
        
        print("17-Day European Trip Itinerary:")
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