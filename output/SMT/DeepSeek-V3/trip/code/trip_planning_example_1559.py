from z3 import *

def plan_trip():
    # Initialize solver
    s = Solver()

    # Cities
    cities = ['Valencia', 'Oslo', 'Lyon', 'Prague', 'Paris', 
              'Nice', 'Seville', 'Tallinn', 'Mykonos', 'Lisbon']
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
        'Valencia': 2,
        'Oslo': 3,
        'Lyon': 4,
        'Prague': 3,
        'Paris': 4,
        'Nice': 4,
        'Seville': 5,
        'Tallinn': 2,
        'Mykonos': 5,
        'Lisbon': 2
    }
    
    for city, duration in stay_durations.items():
        idx = city_indices[city]
        # Total days in city must equal duration
        s.add(Sum([If(city_day[idx][day-1], 1, 0) for day in day_range]) == duration)
    
    # 3. Fixed events
    # Friends in Valencia between day 3-4
    valencia_idx = city_indices['Valencia']
    s.add(Or(city_day[valencia_idx][2], city_day[valencia_idx][3]))  # Days 3-4
    
    # Friend in Oslo between day 13-15
    oslo_idx = city_indices['Oslo']
    s.add(Or([city_day[oslo_idx][d] for d in range(12, 15)]))  # Days 13-15
    
    # Annual show in Seville between day 5-9
    seville_idx = city_indices['Seville']
    s.add(Or([city_day[seville_idx][d] for d in range(4, 9)]))  # Days 5-9
    
    # Wedding in Mykonos between day 21-25
    mykonos_idx = city_indices['Mykonos']
    s.add(And([city_day[mykonos_idx][d] for d in range(20, 25)]))  # Days 21-25
    
    # 4. Flight connections (direct flights)
    connections = {
        'Lisbon': ['Paris', 'Seville', 'Prague', 'Nice', 'Oslo', 'Lyon', 'Valencia'],
        'Lyon': ['Nice', 'Prague', 'Paris', 'Valencia', 'Oslo', 'Lisbon'],
        'Tallinn': ['Oslo', 'Prague', 'Paris'],
        'Prague': ['Lyon', 'Lisbon', 'Oslo', 'Paris', 'Valencia', 'Tallinn'],
        'Paris': ['Lisbon', 'Oslo', 'Valencia', 'Nice', 'Lyon', 'Seville', 'Tallinn', 'Prague'],
        'Nice': ['Lyon', 'Paris', 'Mykonos', 'Lisbon', 'Oslo'],
        'Seville': ['Paris', 'Lisbon', 'Valencia'],
        'Oslo': ['Tallinn', 'Paris', 'Prague', 'Nice', 'Lyon', 'Lisbon'],
        'Valencia': ['Paris', 'Lisbon', 'Lyon', 'Prague', 'Seville'],
        'Mykonos': ['Nice']
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
        print("25-Day European Trip Itinerary:")
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