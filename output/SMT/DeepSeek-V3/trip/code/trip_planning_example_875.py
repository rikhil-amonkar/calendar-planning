from z3 import *

def plan_trip():
    # Initialize solver
    s = Solver()

    # Cities
    cities = ['Stuttgart', 'Edinburgh', 'Athens', 'Split', 'Krakow', 'Venice', 'Mykonos']
    city_indices = {city: idx for idx, city in enumerate(cities)}
    
    # Days (1-20)
    days = 20
    day_range = range(1, days + 1)
    
    # Create variables: city_day[i][j] is True if in city i on day j
    city_day = [[Bool(f'city_{i}_day_{j}') for j in day_range] for i in range(len(cities))]
    
    # Constraints
    
    # 1. Each day must be in exactly one city
    for day in day_range:
        s.add(ExactlyOne([city_day[i][day-1] for i in range(len(cities))]))
    
    # 2. Stay durations
    stay_durations = {
        'Stuttgart': 3,
        'Edinburgh': 4,
        'Athens': 4,
        'Split': 2,
        'Krakow': 4,
        'Venice': 5,
        'Mykonos': 4
    }
    
    for city, duration in stay_durations.items():
        idx = city_indices[city]
        # Total days in city must equal duration
        s.add(Sum([If(city_day[idx][day-1], 1, 0) for day in day_range]) == duration)
    
    # 3. Fixed events
    # Workshop in Stuttgart between day 11-13
    stuttgart_idx = city_indices['Stuttgart']
    s.add(Or([city_day[stuttgart_idx][d] for d in range(10, 13)]))  # Days 11-13
    
    # Friends in Split between day 13-14
    split_idx = city_indices['Split']
    s.add(Or(city_day[split_idx][12], city_day[split_idx][13]))  # Days 13-14
    
    # Friend in Krakow between day 8-11
    krakow_idx = city_indices['Krakow']
    s.add(Or([city_day[krakow_idx][d] for d in range(7, 11)]))  # Days 8-11
    
    # 4. Flight connections (direct flights)
    connections = {
        'Krakow': ['Split', 'Stuttgart', 'Edinburgh'],
        'Split': ['Krakow', 'Athens', 'Stuttgart'],
        'Edinburgh': ['Krakow', 'Stuttgart', 'Athens', 'Venice'],
        'Venice': ['Stuttgart', 'Edinburgh', 'Athens'],
        'Stuttgart': ['Venice', 'Krakow', 'Edinburgh', 'Athens', 'Split'],
        'Athens': ['Split', 'Stuttgart', 'Edinburgh', 'Venice', 'Mykonos'],
        'Mykonos': ['Athens']
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
        print("20-Day European Trip Itinerary:")
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