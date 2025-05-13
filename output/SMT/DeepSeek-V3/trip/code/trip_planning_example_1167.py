from z3 import *

def plan_trip():
    # Initialize solver
    s = Solver()

    # Cities
    cities = ['Dublin', 'Krakow', 'Istanbul', 'Venice', 'Naples', 
              'Brussels', 'Mykonos', 'Frankfurt']
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
        'Dublin': 5,
        'Krakow': 4,
        'Istanbul': 3,
        'Venice': 3,
        'Naples': 4,
        'Brussels': 2,
        'Mykonos': 4,
        'Frankfurt': 3
    }
    
    for city, duration in stay_durations.items():
        idx = city_indices[city]
        # Total days in city must equal duration
        s.add(Sum([If(city_day[idx][day-1], 1, 0) for day in day_range]) == duration)
    
    # 3. Fixed events
    # Annual show in Dublin between day 11-15
    dublin_idx = city_indices['Dublin']
    s.add(Or([city_day[dublin_idx][d] for d in range(10, 15)]))  # Days 11-15
    
    # Friend in Istanbul between day 9-11
    istanbul_idx = city_indices['Istanbul']
    s.add(Or([city_day[istanbul_idx][d] for d in range(8, 11)]))  # Days 9-11
    
    # Relatives in Mykonos between day 1-4
    mykonos_idx = city_indices['Mykonos']
    s.add(Or([city_day[mykonos_idx][d] for d in range(4)]))  # Days 1-4
    
    # Friends in Frankfurt between day 15-17
    frankfurt_idx = city_indices['Frankfurt']
    s.add(Or([city_day[frankfurt_idx][d] for d in range(14, 17)]))  # Days 15-17
    
    # 4. Flight connections (direct flights)
    connections = {
        'Dublin': ['Brussels', 'Naples', 'Krakow', 'Istanbul', 'Venice', 'Frankfurt'],
        'Krakow': ['Frankfurt', 'Brussels', 'Istanbul', 'Dublin'],
        'Istanbul': ['Venice', 'Naples', 'Frankfurt', 'Brussels', 'Krakow', 'Dublin'],
        'Venice': ['Istanbul', 'Frankfurt', 'Brussels', 'Naples', 'Dublin'],
        'Naples': ['Mykonos', 'Dublin', 'Istanbul', 'Brussels', 'Frankfurt', 'Venice'],
        'Brussels': ['Dublin', 'Krakow', 'Naples', 'Istanbul', 'Venice', 'Frankfurt'],
        'Mykonos': ['Naples'],
        'Frankfurt': ['Krakow', 'Brussels', 'Istanbul', 'Venice', 'Naples', 'Dublin']
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