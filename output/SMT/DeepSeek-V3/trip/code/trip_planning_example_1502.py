from z3 import *

def plan_trip():
    # Initialize solver
    s = Solver()

    # Cities
    cities = ['Santorini', 'Valencia', 'Madrid', 'Seville', 'Bucharest',
              'Vienna', 'Riga', 'Tallinn', 'Krakow', 'Frankfurt']
    city_indices = {city: idx for idx, city in enumerate(cities)}
    
    # Days (1-27)
    days = 27
    day_range = range(1, days + 1)
    
    # Create variables: city_day[i][j] is True if in city i on day j
    city_day = [[Bool(f'city_{i}_day_{j}') for j in day_range] for i in range(len(cities))]
    
    # Constraints
    
    # 1. Each day must be in exactly one city
    for day in day_range:
        s.add(ExactlyOne([city_day[i][day-1] for i in range(len(cities))]))
    
    # 2. Stay durations
    stay_durations = {
        'Santorini': 3,
        'Valencia': 4,
        'Madrid': 2,
        'Seville': 2,
        'Bucharest': 3,
        'Vienna': 4,
        'Riga': 4,
        'Tallinn': 5,
        'Krakow': 5,
        'Frankfurt': 4
    }
    
    for city, duration in stay_durations.items():
        idx = city_indices[city]
        # Total days in city must equal duration
        s.add(Sum([If(city_day[idx][day-1], 1, 0) for day in day_range]) == duration)
    
    # 3. Fixed events
    # Annual show in Madrid between day 6-7
    madrid_idx = city_indices['Madrid']
    s.add(Or(city_day[madrid_idx][5], city_day[madrid_idx][6]))  # Days 6-7
    
    # Wedding in Vienna between day 3-6
    vienna_idx = city_indices['Vienna']
    s.add(Or([city_day[vienna_idx][d] for d in range(2, 6)]))  # Days 3-6
    
    # Conference in Riga between day 20-23
    riga_idx = city_indices['Riga']
    s.add(Or([city_day[riga_idx][d] for d in range(19, 23)]))  # Days 20-23
    
    # Workshop in Tallinn between day 23-27
    tallinn_idx = city_indices['Tallinn']
    s.add(Or([city_day[tallinn_idx][d] for d in range(22, 27)]))  # Days 23-27
    
    # Friends in Krakow between day 11-15
    krakow_idx = city_indices['Krakow']
    s.add(Or([city_day[krakow_idx][d] for d in range(10, 15)]))  # Days 11-15
    
    # 4. Flight connections (direct flights)
    connections = {
        'Vienna': ['Bucharest', 'Seville', 'Valencia', 'Madrid', 'Krakow', 'Frankfurt', 'Riga', 'Santorini'],
        'Santorini': ['Madrid', 'Bucharest', 'Vienna'],
        'Seville': ['Valencia', 'Vienna', 'Madrid'],
        'Madrid': ['Santorini', 'Valencia', 'Vienna', 'Seville', 'Bucharest', 'Frankfurt'],
        'Valencia': ['Seville', 'Madrid', 'Bucharest', 'Vienna', 'Krakow', 'Frankfurt'],
        'Bucharest': ['Vienna', 'Valencia', 'Santorini', 'Madrid', 'Frankfurt', 'Riga'],
        'Krakow': ['Valencia', 'Frankfurt', 'Vienna'],
        'Frankfurt': ['Valencia', 'Krakow', 'Vienna', 'Tallinn', 'Bucharest', 'Riga', 'Madrid'],
        'Riga': ['Bucharest', 'Vienna', 'Frankfurt', 'Tallinn'],
        'Tallinn': ['Riga', 'Frankfurt']
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
        print("27-Day European Trip Itinerary:")
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