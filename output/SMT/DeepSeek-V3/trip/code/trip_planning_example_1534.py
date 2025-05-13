from z3 import *

def plan_trip():
    # Initialize solver
    s = Solver()

    # Cities
    cities = ['Warsaw', 'Venice', 'Vilnius', 'Salzburg', 'Amsterdam',
              'Barcelona', 'Paris', 'Hamburg', 'Florence', 'Tallinn']
    city_indices = {city: idx for idx, city in enumerate(cities)}
    
    # Days (1-25)
    days = 25
    day_range = range(1, days + 1)
    
    # Create variables: city_day[i][j] is True if in city i on day j
    city_day = [[Bool(f'city_{i}_day_{j}') for j in day_range] for i in range(len(cities))]
    
    # Constraints
    
    # 1. Each day must be in exactly one city
    for day in day_range:
        s.add(ExactlyOne([city_day[i][day-1] for i in range(len(cities))]))
    
    # 2. Stay durations
    stay_durations = {
        'Warsaw': 4,
        'Venice': 3,
        'Vilnius': 3,
        'Salzburg': 4,
        'Amsterdam': 2,
        'Barcelona': 5,
        'Paris': 2,
        'Hamburg': 4,
        'Florence': 5,
        'Tallinn': 2
    }
    
    for city, duration in stay_durations.items():
        idx = city_indices[city]
        # Total days in city must equal duration
        s.add(Sum([If(city_day[idx][day-1], 1, 0) for day in day_range]) == duration)
    
    # 3. Fixed events
    # Wedding in Salzburg between day 22-25
    salzburg_idx = city_indices['Salzburg']
    s.add(And([city_day[salzburg_idx][d] for d in range(21, 25)]))  # Days 22-25
    
    # Friends in Barcelona between day 2-6
    barcelona_idx = city_indices['Barcelona']
    s.add(Or([city_day[barcelona_idx][d] for d in range(1, 6)]))  # Days 2-6
    
    # Workshop in Paris between day 1-2
    paris_idx = city_indices['Paris']
    s.add(And(city_day[paris_idx][0], city_day[paris_idx][1]))  # Days 1-2
    
    # Conference in Hamburg between day 19-22
    hamburg_idx = city_indices['Hamburg']
    s.add(Or([city_day[hamburg_idx][d] for d in range(18, 22)]))  # Days 19-22
    
    # Friend in Tallinn between day 11-12
    tallinn_idx = city_indices['Tallinn']
    s.add(Or(city_day[tallinn_idx][10], city_day[tallinn_idx][11]))  # Days 11-12
    
    # 4. Flight connections (direct flights)
    connections = {
        'Paris': ['Venice', 'Hamburg', 'Vilnius', 'Amsterdam', 'Florence', 'Warsaw', 'Tallinn', 'Barcelona'],
        'Barcelona': ['Amsterdam', 'Warsaw', 'Hamburg', 'Florence', 'Venice', 'Tallinn', 'Paris'],
        'Amsterdam': ['Warsaw', 'Vilnius', 'Hamburg', 'Barcelona', 'Florence', 'Venice', 'Tallinn', 'Paris'],
        'Warsaw': ['Amsterdam', 'Barcelona', 'Venice', 'Vilnius', 'Tallinn', 'Hamburg', 'Paris'],
        'Venice': ['Paris', 'Warsaw', 'Barcelona', 'Hamburg', 'Amsterdam'],
        'Vilnius': ['Amsterdam', 'Paris', 'Warsaw', 'Tallinn'],
        'Hamburg': ['Amsterdam', 'Barcelona', 'Paris', 'Salzburg', 'Venice', 'Warsaw'],
        'Florence': ['Barcelona', 'Paris', 'Amsterdam'],
        'Tallinn': ['Barcelona', 'Warsaw', 'Vilnius', 'Amsterdam', 'Paris'],
        'Salzburg': ['Hamburg']
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