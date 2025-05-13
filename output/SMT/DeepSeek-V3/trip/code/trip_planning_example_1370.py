from z3 import *

def plan_trip():
    # Initialize solver
    s = Solver()

    # Cities
    cities = ['Santorini', 'Krakow', 'Paris', 'Vilnius', 'Munich', 'Geneva', 'Amsterdam', 'Budapest', 'Split']
    city_indices = {city: idx for idx, city in enumerate(cities)}
    
    # Days (1-30)
    days = 30
    day_range = range(1, days + 1)
    
    # Create variables: city_day[i][j] is True if in city i on day j
    city_day = [[Bool(f'city_{i}_day_{j}') for j in day_range] for i in range(len(cities))]
    
    # Constraints
    
    # 1. Each day must be in exactly one city
    for day in day_range:
        s.add(ExactlyOne([city_day[i][day-1] for i in range(len(cities))))
    
    # 2. Stay durations
    stay_durations = {
        'Santorini': 5,
        'Krakow': 5,
        'Paris': 5,
        'Vilnius': 3,
        'Munich': 5,
        'Geneva': 2,
        'Amsterdam': 4,
        'Budapest': 5,
        'Split': 4
    }
    
    for city, duration in stay_durations.items():
        idx = city_indices[city]
        # Total days in city must equal duration
        s.add(Sum([If(city_day[idx][day-1], 1, 0) for day in day_range]) == duration)
    
    # 3. Fixed events
    # Friends in Santorini between day 25-29
    santorini_idx = city_indices['Santorini']
    s.add(Or([city_day[santorini_idx][d] for d in range(24, 29)]))
    
    # Wedding in Krakow between day 18-22
    krakow_idx = city_indices['Krakow']
    s.add(Or([city_day[krakow_idx][d] for d in range(17, 22)]))
    
    # Friend in Paris between day 11-15
    paris_idx = city_indices['Paris']
    s.add(Or([city_day[paris_idx][d] for d in range(10, 15)]))
    
    # 4. Flight connections (direct flights)
    connections = {
        'Paris': ['Krakow', 'Amsterdam', 'Split', 'Geneva', 'Budapest', 'Vilnius', 'Munich'],
        'Krakow': ['Paris', 'Split', 'Vilnius', 'Munich', 'Amsterdam'],
        'Vilnius': ['Munich', 'Split', 'Amsterdam', 'Paris', 'Krakow'],
        'Munich': ['Split', 'Amsterdam', 'Geneva', 'Krakow', 'Budapest', 'Paris', 'Vilnius'],
        'Geneva': ['Paris', 'Amsterdam', 'Split', 'Budapest', 'Munich', 'Santorini'],
        'Amsterdam': ['Paris', 'Geneva', 'Split', 'Budapest', 'Munich', 'Vilnius', 'Krakow', 'Santorini'],
        'Budapest': ['Amsterdam', 'Geneva', 'Paris', 'Munich'],
        'Split': ['Paris', 'Krakow', 'Munich', 'Geneva', 'Amsterdam', 'Vilnius'],
        'Santorini': ['Geneva', 'Amsterdam']
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
        print("30-Day European Trip Itinerary:")
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