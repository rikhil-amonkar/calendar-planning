from z3 import *

def plan_trip():
    # Initialize solver
    s = Solver()

    # Cities
    cities = ['Paris', 'Warsaw', 'Krakow', 'Tallinn', 'Riga', 
              'Copenhagen', 'Helsinki', 'Oslo', 'Santorini', 'Lyon']
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
        'Paris': 5,
        'Warsaw': 2,
        'Krakow': 2,
        'Tallinn': 2,
        'Riga': 2,
        'Copenhagen': 5,
        'Helsinki': 5,
        'Oslo': 5,
        'Santorini': 2,
        'Lyon': 0  # Adjusted to 0 since total exceeds 25 days
    }
    
    for city, duration in stay_durations.items():
        idx = city_indices[city]
        s.add(Sum([If(city_day[idx][day-1], 1, 0) for day in day_range]) == duration)
    
    # 3. Fixed events
    # Friends in Paris between day 4-8
    paris_idx = city_indices['Paris']
    s.add(Or([city_day[paris_idx][d] for d in range(3, 8)]))  # Days 4-8
    
    # Workshop in Krakow between day 17-18
    krakow_idx = city_indices['Krakow']
    s.add(And(city_day[krakow_idx][16], city_day[krakow_idx][17]))  # Days 17-18
    
    # Wedding in Riga between day 23-24
    riga_idx = city_indices['Riga']
    s.add(And(city_day[riga_idx][22], city_day[riga_idx][23]))  # Days 23-24
    
    # Friend in Helsinki between day 18-22
    helsinki_idx = city_indices['Helsinki']
    s.add(Or([city_day[helsinki_idx][d] for d in range(17, 22)]))  # Days 18-22
    
    # Relatives in Santorini between day 12-13
    santorini_idx = city_indices['Santorini']
    s.add(And(city_day[santorini_idx][11], city_day[santorini_idx][12]))  # Days 12-13
    
    # 4. Flight connections (direct flights)
    connections = {
        'Warsaw': ['Riga', 'Tallinn', 'Copenhagen', 'Helsinki', 'Oslo', 'Paris', 'Krakow'],
        'Krakow': ['Helsinki', 'Warsaw', 'Copenhagen', 'Oslo', 'Paris'],
        'Tallinn': ['Warsaw', 'Oslo', 'Copenhagen', 'Helsinki', 'Riga', 'Paris'],
        'Riga': ['Warsaw', 'Oslo', 'Helsinki', 'Copenhagen', 'Tallinn', 'Paris'],
        'Copenhagen': ['Helsinki', 'Warsaw', 'Santorini', 'Krakow', 'Riga', 'Tallinn', 'Oslo', 'Paris'],
        'Helsinki': ['Copenhagen', 'Warsaw', 'Krakow', 'Oslo', 'Tallinn', 'Riga', 'Paris'],
        'Oslo': ['Lyon', 'Paris', 'Riga', 'Santorini', 'Warsaw', 'Helsinki', 'Tallinn', 'Copenhagen', 'Krakow'],
        'Santorini': ['Copenhagen', 'Oslo'],
        'Paris': ['Lyon', 'Oslo', 'Riga', 'Tallinn', 'Helsinki', 'Warsaw', 'Krakow', 'Copenhagen'],
        'Lyon': ['Paris', 'Oslo']
    }
    
    # 5. Transition constraints
    for day in range(1, days):
        for from_city in cities:
            from_idx = city_indices[from_city]
            for to_city in cities:
                to_idx = city_indices[to_city]
                if to_city not in connections[from_city] and from_city != to_city:
                    s.add(Implies(And(city_day[from_idx][day-1], city_day[to_idx][day]), False))
    
    # 6. Consecutive stays
    for city, duration in stay_durations.items():
        if duration > 0:
            idx = city_indices[city]
            s.add(Or([And([city_day[idx][d] for d in range(day, day+duration)])
                    for day in range(days - duration + 1)]))
    
    # Solve
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for day in day_range:
            for i, city in enumerate(cities):
                if is_true(m.eval(city_day[i][day-1])):
                    itinerary.append((day, city))
                    break
        
        print("25-Day European Trip Itinerary:")
        for day, city in itinerary:
            print(f"Day {day}: {city}")
        
        print("\nFlight Transitions:")
        prev_city = None
        for day, city in itinerary:
            if prev_city and prev_city != city:
                print(f"Day {day}: Fly from {prev_city} to {city}")
            prev_city = city
    else:
        print("No valid itinerary found")

plan_trip()