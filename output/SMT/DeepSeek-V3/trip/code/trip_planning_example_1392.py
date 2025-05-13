from z3 import *

def plan_trip():
    # Initialize solver
    s = Solver()

    # Cities
    cities = ['Naples', 'Valencia', 'Stuttgart', 'Split', 'Venice', 'Amsterdam', 'Nice', 'Barcelona', 'Porto']
    city_indices = {city: idx for idx, city in enumerate(cities)}
    
    # Days (1-24)
    days = 24
    day_range = range(1, days + 1)
    
    # Create variables: city_day[i][j] is True if in city i on day j
    city_day = [[Bool(f'city_{i}_day_{j}') for j in day_range] for i in range(len(cities))]
    
    # Constraints
    
    # 1. Each day must be in exactly one city
    for day in day_range:
        s.add(ExactlyOne([city_day[i][day-1] for i in range(len(cities))])
    
    # 2. Stay durations
    stay_durations = {
        'Naples': 3,
        'Valencia': 5,
        'Stuttgart': 2,
        'Split': 5,
        'Venice': 5,
        'Amsterdam': 4,
        'Nice': 2,
        'Barcelona': 2,
        'Porto': 4
    }
    
    for city, duration in stay_durations.items():
        idx = city_indices[city]
        # Total days in city must equal duration
        s.add(Sum([If(city_day[idx][day-1], 1, 0) for day in day_range]) == duration)
    
    # 3. Fixed events
    # Meet friend in Naples between day 18-20
    naples_idx = city_indices['Naples']
    s.add(Or([city_day[naples_idx][d] for d in range(17, 20)]))
    
    # Conference in Venice between day 6-10
    venice_idx = city_indices['Venice']
    s.add(Or([city_day[venice_idx][d] for d in range(5, 10)]))
    
    # Friends in Nice between day 23-24
    nice_idx = city_indices['Nice']
    s.add(Or(city_day[nice_idx][22], city_day[nice_idx][23]))
    
    # Workshop in Barcelona between day 5-6
    barcelona_idx = city_indices['Barcelona']
    s.add(Or(city_day[barcelona_idx][4], city_day[barcelona_idx][5]))
    
    # 4. Flight connections (direct flights)
    connections = {
        'Venice': ['Nice', 'Amsterdam', 'Stuttgart', 'Naples'],
        'Naples': ['Amsterdam', 'Split', 'Valencia', 'Barcelona', 'Nice', 'Stuttgart'],
        'Barcelona': ['Nice', 'Porto', 'Naples', 'Valencia', 'Venice', 'Amsterdam', 'Stuttgart', 'Split'],
        'Stuttgart': ['Valencia', 'Porto', 'Split', 'Amsterdam', 'Naples', 'Venice', 'Barcelona'],
        'Split': ['Stuttgart', 'Naples', 'Amsterdam', 'Barcelona'],
        'Valencia': ['Stuttgart', 'Amsterdam', 'Naples', 'Porto', 'Barcelona'],
        'Amsterdam': ['Naples', 'Nice', 'Valencia', 'Venice', 'Porto', 'Split', 'Stuttgart', 'Barcelona'],
        'Nice': ['Venice', 'Barcelona', 'Amsterdam', 'Naples', 'Porto'],
        'Porto': ['Stuttgart', 'Barcelona', 'Nice', 'Amsterdam', 'Valencia']
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
        print("24-Day European Trip Itinerary:")
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