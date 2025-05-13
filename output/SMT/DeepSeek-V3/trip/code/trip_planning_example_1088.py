from z3 import *

def plan_trip():
    # Initialize solver
    s = Solver()

    # Cities
    cities = ['Reykjavik', 'Stuttgart', 'Oslo', 'Split', 'Geneva', 'Porto', 'Tallinn', 'Stockholm']
    city_indices = {city: idx for idx, city in enumerate(cities)}
    
    # Days (1-21)
    days = 21
    day_range = range(1, days + 1)
    
    # Create variables: city_day[i][j] is True if in city i on day j
    city_day = [[Bool(f'city_{i}_day_{j}') for j in day_range] for i in range(len(cities))]
    
    # Constraints
    
    # 1. Each day must be in exactly one city
    for day in day_range:
        s.add(ExactlyOne([city_day[i][day-1] for i in range(len(cities))]))
    
    # 2. Stay durations
    stay_durations = {
        'Oslo': 5,
        'Stuttgart': 5,
        'Reykjavik': 2,
        'Split': 3,
        'Geneva': 2,
        'Porto': 3,
        'Tallinn': 5,
        'Stockholm': 3
    }
    
    for city, duration in stay_durations.items():
        idx = city_indices[city]
        # Total days in city must equal duration
        s.add(Sum([If(city_day[idx][day-1], 1, 0) for day in day_range]) == duration)
    
    # 3. Fixed events
    # Conference in Reykjavik on days 1-2
    reyk_idx = city_indices['Reykjavik']
    s.add(city_day[reyk_idx][0])  # Day 1
    s.add(city_day[reyk_idx][1])  # Day 2
    
    # Workshop in Porto between day 19-21
    porto_idx = city_indices['Porto']
    s.add(Or(city_day[porto_idx][18], city_day[porto_idx][19], city_day[porto_idx][20]))
    
    # Meet friend in Stockholm between day 2-4
    stock_idx = city_indices['Stockholm']
    s.add(Or(city_day[stock_idx][1], city_day[stock_idx][2], city_day[stock_idx][3]))
    
    # 4. Flight connections (direct flights)
    connections = {
        'Reykjavik': ['Stuttgart', 'Stockholm', 'Tallinn', 'Oslo'],
        'Stockholm': ['Oslo', 'Stuttgart', 'Split', 'Geneva', 'Reykjavik'],
        'Stuttgart': ['Porto', 'Split', 'Reykjavik', 'Stockholm'],
        'Oslo': ['Split', 'Geneva', 'Porto', 'Stockholm', 'Tallinn', 'Reykjavik'],
        'Split': ['Stuttgart', 'Geneva', 'Stockholm', 'Oslo'],
        'Geneva': ['Porto', 'Split', 'Stockholm', 'Oslo'],
        'Porto': ['Stuttgart', 'Geneva', 'Oslo'],
        'Tallinn': ['Oslo', 'Reykjavik']
    }
    
    # 5. Transition constraints - can only move between connected cities
    for day in range(1, days):
        for from_city in cities:
            from_idx = city_indices[from_city]
            for to_city in cities:
                to_idx = city_indices[to_city]
                if to_city not in connections[from_city] and from_city != to_city:
                    # If in from_city today, can't be in to_city tomorrow unless connected
                    s.add(Implies(And(city_day[from_idx][day-1], city_day[to_idx][day]),
                          False))
    
    # 6. Stay must be consecutive days (simplified - at least one stay of full duration)
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
        print("21-Day European Trip Itinerary:")
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