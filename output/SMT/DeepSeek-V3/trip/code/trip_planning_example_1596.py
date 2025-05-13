from z3 import *

def plan_trip():
    # Initialize solver
    s = Solver()

    # Cities
    cities = ['Bucharest', 'Krakow', 'Munich', 'Barcelona', 'Warsaw',
              'Budapest', 'Stockholm', 'Riga', 'Edinburgh', 'Vienna']
    city_indices = {city: idx for idx, city in enumerate(cities)}
    
    # Days (1-32)
    days = 32
    day_range = range(1, days + 1)
    
    # Create variables: city_day[i][j] is True if in city i on day j
    city_day = [[Bool(f'city_{i}_day_{j}') for j in day_range] for i in range(len(cities))]
    
    # Constraints
    
    # 1. Each day must be in exactly one city
    for day in day_range:
        s.add(ExactlyOne([city_day[i][day-1] for i in range(len(cities))))
    
    # 2. Stay durations
    stay_durations = {
        'Bucharest': 2,
        'Krakow': 4,
        'Munich': 3,
        'Barcelona': 5,
        'Warsaw': 5,
        'Budapest': 5,
        'Stockholm': 2,
        'Riga': 5,
        'Edinburgh': 5,
        'Vienna': 5
    }
    
    for city, duration in stay_durations.items():
        idx = city_indices[city]
        # Total days in city must equal duration
        s.add(Sum([If(city_day[idx][day-1], 1, 0) for day in day_range]) == duration)
    
    # 3. Fixed events
    # Workshop in Munich between day 18-20
    munich_idx = city_indices['Munich']
    s.add(Or([city_day[munich_idx][d] for d in range(17, 20)]))  # Days 18-20
    
    # Conference in Warsaw between day 25-29
    warsaw_idx = city_indices['Warsaw']
    s.add(Or([city_day[warsaw_idx][d] for d in range(24, 29)]))  # Days 25-29
    
    # Annual show in Budapest between day 9-13
    budapest_idx = city_indices['Budapest']
    s.add(Or([city_day[budapest_idx][d] for d in range(8, 13)]))  # Days 9-13
    
    # Friends in Stockholm between day 17-18
    stockholm_idx = city_indices['Stockholm']
    s.add(Or(city_day[stockholm_idx][16], city_day[stockholm_idx][17]))  # Days 17-18
    
    # Friend in Edinburgh between day 1-5
    edinburgh_idx = city_indices['Edinburgh']
    s.add(Or([city_day[edinburgh_idx][d] for d in range(5)]))  # Days 1-5
    
    # 4. Flight connections (direct flights)
    connections = {
        'Budapest': ['Munich', 'Vienna', 'Warsaw', 'Edinburgh', 'Barcelona', 'Bucharest'],
        'Bucharest': ['Riga', 'Munich', 'Warsaw', 'Barcelona', 'Vienna'],
        'Munich': ['Krakow', 'Warsaw', 'Bucharest', 'Budapest', 'Barcelona', 'Edinburgh', 'Stockholm', 'Vienna', 'Riga'],
        'Barcelona': ['Warsaw', 'Munich', 'Stockholm', 'Edinburgh', 'Riga', 'Budapest', 'Krakow', 'Bucharest', 'Vienna'],
        'Warsaw': ['Munich', 'Barcelona', 'Krakow', 'Budapest', 'Bucharest', 'Vienna', 'Riga', 'Stockholm'],
        'Stockholm': ['Edinburgh', 'Krakow', 'Barcelona', 'Munich', 'Riga', 'Vienna', 'Warsaw'],
        'Riga': ['Bucharest', 'Barcelona', 'Edinburgh', 'Munich', 'Vienna', 'Warsaw', 'Stockholm'],
        'Edinburgh': ['Stockholm', 'Krakow', 'Budapest', 'Barcelona', 'Munich', 'Riga'],
        'Vienna': ['Budapest', 'Krakow', 'Bucharest', 'Munich', 'Stockholm', 'Riga', 'Warsaw', 'Barcelona'],
        'Krakow': ['Munich', 'Edinburgh', 'Stockholm', 'Vienna', 'Warsaw', 'Barcelona']
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
        print("32-Day European Trip Itinerary:")
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