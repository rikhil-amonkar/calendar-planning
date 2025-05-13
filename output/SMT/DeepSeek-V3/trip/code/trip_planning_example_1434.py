from z3 import *

def plan_trip():
    # Initialize solver
    s = Solver()

    # Cities
    cities = ['Rome', 'Mykonos', 'Lisbon', 'Frankfurt', 'Nice', 
              'Stuttgart', 'Venice', 'Dublin', 'Bucharest', 'Seville']
    city_indices = {city: idx for idx, city in enumerate(cities)}
    
    # Days (1-23)
    days = 23
    day_range = range(1, days + 1)
    
    # Create variables: city_day[i][j] is True if in city i on day j
    city_day = [[Bool(f'city_{i}_day_{j}') for j in day_range] for i in range(len(cities))]
    
    # Constraints
    
    # 1. Each day must be in exactly one city
    for day in day_range:
        s.add(ExactlyOne([city_day[i][day-1] for i in range(len(cities))]))
    
    # 2. Stay durations
    stay_durations = {
        'Rome': 3,
        'Mykonos': 2,
        'Lisbon': 2,
        'Frankfurt': 5,
        'Nice': 3,
        'Stuttgart': 4,
        'Venice': 4,
        'Dublin': 2,
        'Bucharest': 2,
        'Seville': 5
    }
    
    for city, duration in stay_durations.items():
        idx = city_indices[city]
        # Total days in city must equal duration
        s.add(Sum([If(city_day[idx][day-1], 1, 0) for day in day_range]) == duration)
    
    # 3. Fixed events
    # Friends in Mykonos between day 10-11
    mykonos_idx = city_indices['Mykonos']
    s.add(Or(city_day[mykonos_idx][9], city_day[mykonos_idx][10]))  # Days 10-11
    
    # Wedding in Frankfurt between day 1-5
    frankfurt_idx = city_indices['Frankfurt']
    s.add(And([city_day[frankfurt_idx][d] for d in range(5)]))  # Days 1-5
    
    # Conference in Seville between day 13-17
    seville_idx = city_indices['Seville']
    s.add(Or([city_day[seville_idx][d] for d in range(12, 17)]))  # Days 13-17
    
    # 4. Flight connections (direct flights)
    connections = {
        'Rome': ['Stuttgart', 'Venice', 'Mykonos', 'Seville', 'Frankfurt', 'Bucharest', 'Dublin', 'Lisbon', 'Nice'],
        'Mykonos': ['Rome', 'Nice'],
        'Lisbon': ['Seville', 'Bucharest', 'Venice', 'Dublin', 'Rome', 'Frankfurt', 'Nice', 'Stuttgart'],
        'Frankfurt': ['Venice', 'Rome', 'Dublin', 'Nice', 'Stuttgart', 'Bucharest', 'Lisbon'],
        'Nice': ['Mykonos', 'Venice', 'Dublin', 'Rome', 'Frankfurt', 'Lisbon'],
        'Stuttgart': ['Rome', 'Venice', 'Frankfurt', 'Lisbon'],
        'Venice': ['Rome', 'Frankfurt', 'Stuttgart', 'Lisbon', 'Nice', 'Dublin'],
        'Dublin': ['Bucharest', 'Lisbon', 'Rome', 'Nice', 'Frankfurt', 'Venice', 'Seville'],
        'Bucharest': ['Dublin', 'Lisbon', 'Rome', 'Frankfurt'],
        'Seville': ['Lisbon', 'Rome', 'Dublin']
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
        print("23-Day European Trip Itinerary:")
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