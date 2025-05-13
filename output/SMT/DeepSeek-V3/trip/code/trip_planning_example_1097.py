from z3 import *

def plan_trip():
    # Initialize solver
    s = Solver()

    # Cities
    cities = ['Reykjavik', 'Riga', 'Oslo', 'Lyon', 'Dubrovnik', 'Madrid', 'Warsaw', 'London']
    city_indices = {city: idx for idx, city in enumerate(cities)}
    
    # Days (1-18)
    days = 18
    day_range = range(1, days + 1)
    
    # Create variables: city_day[i][j] is True if in city i on day j
    city_day = [[Bool(f'city_{i}_day_{j}') for j in day_range] for i in range(len(cities))]
    
    # Constraints
    
    # 1. Each day must be in exactly one city
    for day in day_range:
        s.add(ExactlyOne([city_day[i][day-1] for i in range(len(cities))]))
    
    # 2. Stay durations
    stay_durations = {
        'Reykjavik': 4,
        'Riga': 2,
        'Oslo': 3,
        'Lyon': 5,
        'Dubrovnik': 2,
        'Madrid': 2,
        'Warsaw': 4,
        'London': 3
    }
    
    for city, duration in stay_durations.items():
        idx = city_indices[city]
        # Total days in city must equal duration
        s.add(Sum([If(city_day[idx][day-1], 1, 0) for day in day_range]) == duration)
    
    # 3. Fixed events
    # Meet friend in Riga between day 4-5
    riga_idx = city_indices['Riga']
    s.add(Or(city_day[riga_idx][3], city_day[riga_idx][4]))  # Days 4-5
    
    # Wedding in Dubrovnik between day 7-8
    dubrovnik_idx = city_indices['Dubrovnik']
    s.add(Or(city_day[dubrovnik_idx][6], city_day[dubrovnik_idx][7]))  # Days 7-8
    
    # 4. Flight connections (direct flights)
    connections = {
        'Warsaw': ['Reykjavik', 'Riga', 'London', 'Madrid', 'Oslo'],
        'Oslo': ['Madrid', 'Dubrovnik', 'Reykjavik', 'Riga', 'Lyon', 'London'],
        'Riga': ['Oslo', 'Warsaw'],
        'Lyon': ['London', 'Madrid', 'Oslo'],
        'Dubrovnik': ['Madrid', 'Oslo'],
        'Madrid': ['London', 'Oslo', 'Lyon', 'Dubrovnik', 'Warsaw'],
        'Reykjavik': ['Madrid', 'Warsaw', 'Oslo', 'London'],
        'London': ['Lyon', 'Madrid', 'Warsaw', 'Oslo', 'Reykjavik']
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
        print("18-Day European Trip Itinerary:")
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