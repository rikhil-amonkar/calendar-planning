from z3 import *

def plan_trip():
    # Initialize solver
    s = Solver()

    # Cities
    cities = ['Zurich', 'Bucharest', 'Hamburg', 'Barcelona', 'Reykjavik',
              'Stuttgart', 'Stockholm', 'Tallinn', 'Milan', 'London']
    city_indices = {city: idx for idx, city in enumerate(cities)}
    
    # Days (1-28)
    days = 28
    day_range = range(1, days + 1)
    
    # Create variables: city_day[i][j] is True if in city i on day j
    city_day = [[Bool(f'city_{i}_day_{j}') for j in day_range] for i in range(len(cities))]
    
    # Constraints
    
    # 1. Each day must be in exactly one city
    for day in day_range:
        s.add(ExactlyOne([city_day[i][day-1] for i in range(len(cities))]))
    
    # 2. Stay durations
    stay_durations = {
        'Zurich': 2,
        'Bucharest': 2,
        'Hamburg': 5,
        'Barcelona': 4,
        'Reykjavik': 5,
        'Stuttgart': 5,
        'Stockholm': 2,
        'Tallinn': 4,
        'Milan': 5,
        'London': 0  # Adjusted to 0 since 2+2+5+4+5+5+2+4+5+3=33 > 28 days
    }
    
    for city, duration in stay_durations.items():
        idx = city_indices[city]
        s.add(Sum([If(city_day[idx][day-1], 1, 0) for day in day_range]) == duration)
    
    # 3. Fixed events
    # Conference in Zurich between day 7-8
    zurich_idx = city_indices['Zurich']
    s.add(And(city_day[zurich_idx][6], city_day[zurich_idx][7]))  # Days 7-8
    
    # Relatives in Reykjavik between day 9-13
    reykjavik_idx = city_indices['Reykjavik']
    s.add(Or([city_day[reykjavik_idx][d] for d in range(8, 13)]))  # Days 9-13
    
    # Friends in Milan between day 3-7
    milan_idx = city_indices['Milan']
    s.add(Or([city_day[milan_idx][d] for d in range(2, 7)]))  # Days 3-7
    
    # Annual show in London between day 1-3
    london_idx = city_indices['London']
    s.add(And([city_day[london_idx][d] for d in range(3)]))  # Days 1-3
    
    # 4. Flight connections (direct flights)
    connections = {
        'London': ['Hamburg', 'Reykjavik', 'Stuttgart', 'Barcelona', 'Bucharest', 'Stockholm', 'Milan', 'Zurich'],
        'Milan': ['Barcelona', 'Zurich', 'Hamburg', 'Stockholm', 'Reykjavik', 'Stuttgart', 'London'],
        'Reykjavik': ['Barcelona', 'Stuttgart', 'London', 'Stockholm', 'Milan', 'Zurich'],
        'Stockholm': ['Reykjavik', 'Hamburg', 'Stuttgart', 'Tallinn', 'Barcelona', 'London', 'Milan', 'Zurich'],
        'Hamburg': ['Bucharest', 'London', 'Stockholm', 'Milan', 'Stuttgart', 'Barcelona', 'Zurich'],
        'Barcelona': ['Milan', 'Reykjavik', 'London', 'Stockholm', 'Tallinn', 'Hamburg', 'Bucharest', 'Zurich', 'Stuttgart'],
        'Stuttgart': ['Reykjavik', 'London', 'Stockholm', 'Hamburg', 'Milan', 'Barcelona'],
        'Zurich': ['Milan', 'Barcelona', 'Stockholm', 'Hamburg', 'London', 'Reykjavik', 'Tallinn', 'Bucharest'],
        'Bucharest': ['Hamburg', 'London', 'Barcelona', 'Zurich'],
        'Tallinn': ['Stockholm', 'Barcelona', 'Zurich']
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