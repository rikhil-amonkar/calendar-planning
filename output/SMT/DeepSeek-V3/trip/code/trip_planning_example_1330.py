from z3 import *

def plan_trip():
    # Initialize solver
    s = Solver()

    # Cities
    cities = ['Salzburg', 'Venice', 'Bucharest', 'Brussels', 'Hamburg', 
              'Copenhagen', 'Nice', 'Zurich', 'Naples']
    city_indices = {city: idx for idx, city in enumerate(cities)}
    
    # Days (1-25)
    days = 25
    day_range = range(1, days + 1)
    
    # Create variables: city_day[i][j] is True if in city i on day j
    city_day = [[Bool(f'city_{i}_day_{j}') for j in day_range] for i in range(len(cities))]
    
    # Constraints
    
    # 1. Each day must be in exactly one city
    for day in day_range:
        s.add(ExactlyOne([city_day[i][day-1] for i in range(len(cities))))
    
    # 2. Stay durations
    stay_durations = {
        'Salzburg': 2,
        'Venice': 5,
        'Bucharest': 4,
        'Brussels': 2,
        'Hamburg': 4,
        'Copenhagen': 4,
        'Nice': 3,
        'Zurich': 5,
        'Naples': 4
    }
    
    for city, duration in stay_durations.items():
        idx = city_indices[city]
        s.add(Sum([If(city_day[idx][day-1], 1, 0) for day in day_range]) == duration)
    
    # 3. Fixed events
    # Friends in Brussels between day 21-22
    brussels_idx = city_indices['Brussels']
    s.add(And(city_day[brussels_idx][20], city_day[brussels_idx][21]))  # Days 21-22
    
    # Wedding in Copenhagen between day 18-21
    copenhagen_idx = city_indices['Copenhagen']
    s.add(Or([city_day[copenhagen_idx][d] for d in range(17, 21)]))  # Days 18-21
    
    # Relatives in Nice between day 9-11
    nice_idx = city_indices['Nice']
    s.add(And([city_day[nice_idx][d] for d in range(8, 11)]))  # Days 9-11
    
    # Workshop in Naples between day 22-25
    naples_idx = city_indices['Naples']
    s.add(And([city_day[naples_idx][d] for d in range(21, 25)]))  # Days 22-25
    
    # 4. Flight connections (direct flights)
    connections = {
        'Zurich': ['Brussels', 'Nice', 'Naples', 'Copenhagen', 'Bucharest', 'Venice', 'Hamburg'],
        'Bucharest': ['Copenhagen', 'Brussels', 'Naples', 'Hamburg', 'Zurich'],
        'Venice': ['Brussels', 'Naples', 'Copenhagen', 'Zurich', 'Nice', 'Hamburg'],
        'Nice': ['Zurich', 'Brussels', 'Naples', 'Hamburg', 'Venice', 'Copenhagen'],
        'Hamburg': ['Nice', 'Bucharest', 'Brussels', 'Copenhagen', 'Zurich', 'Venice', 'Salzburg'],
        'Copenhagen': ['Bucharest', 'Brussels', 'Naples', 'Venice', 'Zurich', 'Nice', 'Hamburg'],
        'Brussels': ['Zurich', 'Bucharest', 'Venice', 'Nice', 'Hamburg', 'Copenhagen', 'Naples'],
        'Naples': ['Zurich', 'Bucharest', 'Venice', 'Nice', 'Copenhagen', 'Brussels'],
        'Salzburg': ['Hamburg']
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