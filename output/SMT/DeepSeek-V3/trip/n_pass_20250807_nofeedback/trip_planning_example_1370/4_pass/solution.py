from z3 import *

def solve_itinerary():
    # Cities and their required days
    cities = [
        ('Santorini', 5),
        ('Krakow', 5),
        ('Paris', 5),
        ('Vilnius', 3),
        ('Munich', 5),
        ('Geneva', 2),
        ('Amsterdam', 4),
        ('Budapest', 5),
        ('Split', 4)
    ]
    city_names = [city[0] for city in cities]
    city_days = {city[0]: city[1] for city in cities}
    
    # Direct flights
    direct_flights = {
        'Paris': ['Krakow', 'Amsterdam', 'Split', 'Geneva', 'Budapest', 'Vilnius', 'Munich'],
        'Krakow': ['Paris', 'Split', 'Munich', 'Amsterdam', 'Vilnius'],
        'Vilnius': ['Munich', 'Split', 'Amsterdam', 'Paris', 'Krakow'],
        'Munich': ['Vilnius', 'Split', 'Amsterdam', 'Geneva', 'Krakow', 'Paris', 'Budapest'],
        'Geneva': ['Paris', 'Amsterdam', 'Split', 'Munich', 'Budapest', 'Santorini'],
        'Amsterdam': ['Paris', 'Geneva', 'Munich', 'Budapest', 'Split', 'Vilnius', 'Krakow', 'Santorini'],
        'Budapest': ['Amsterdam', 'Paris', 'Geneva', 'Munich'],
        'Split': ['Paris', 'Munich', 'Geneva', 'Amsterdam', 'Krakow', 'Vilnius'],
        'Santorini': ['Geneva', 'Amsterdam']
    }
    
    # Create a Z3 solver
    s = Solver()
    
    # Assign each day to a city (0-8)
    day_assignments = [Int(f'day_{day}') for day in range(1, 31)]
    for day in day_assignments:
        s.add(day >= 0, day < len(city_names))
    
    # Ensure each city has the correct number of days
    for city_idx, city in enumerate(city_names):
        s.add(Sum([If(day_assignments[day] == city_idx, 1, 0) for day in range(30)]) == city_days[city])
    
    # Specific date ranges
    # Santorini between day 25-29 (inclusive)
    for day in range(24, 29):  # days 25-29 (0-based: 24-28)
        s.add(day_assignments[day] == city_names.index('Santorini'))
    
    # Krakow between day 18-22 (inclusive)
    for day in range(17, 22):  # days 18-22 (0-based: 17-21)
        s.add(day_assignments[day] == city_names.index('Krakow'))
    
    # Paris between day 11-15 (inclusive)
    for day in range(10, 15):  # days 11-15 (0-based: 10-14)
        s.add(day_assignments[day] == city_names.index('Paris'))
    
    # Flight transitions: if day i is city A and day i+1 is city B, then there's a direct flight
    for day in range(29):  # days 1-29 (0-based: 0-28)
        current_city = day_assignments[day]
        next_city = day_assignments[day + 1]
        for city_idx in range(len(city_names)):
            for next_city_idx in range(len(city_names)):
                if city_idx != next_city_idx:
                    current_city_name = city_names[city_idx]
                    next_city_name = city_names[next_city_idx]
                    if next_city_name not in direct_flights.get(current_city_name, []):
                        s.add(Not(And(current_city == city_idx, next_city == next_city_idx)))
    
    # Check if the solver can find a solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for day in range(30):
            city_idx = model[day_assignments[day]].as_long()
            itinerary.append({"day": day + 1, "place": city_names[city_idx]})
        
        # Verify transitions
        valid = True
        for i in range(29):
            current_city = itinerary[i]['place']
            next_city = itinerary[i + 1]['place']
            if current_city != next_city and next_city not in direct_flights[current_city]:
                valid = False
                break
        if not valid:
            print("Invalid transitions found.")
            return None
        
        # Verify day counts
        day_counts = {city: 0 for city in city_names}
        for entry in itinerary:
            day_counts[entry['place']] += 1
        for city in city_names:
            if day_counts[city] != city_days[city]:
                print(f"Day count mismatch for {city}: expected {city_days[city]}, got {day_counts[city]}")
                return None
        
        # Verify date ranges
        # Santorini 25-29
        santorini_days = [entry['day'] for entry in itinerary if entry['place'] == 'Santorini']
        if not all(25 <= day <= 29 for day in santorini_days):
            print("Santorini days not in 25-29")
            return None
        # Krakow 18-22
        krakow_days = [entry['day'] for entry in itinerary if entry['place'] == 'Krakow']
        if not all(18 <= day <= 22 for day in krakow_days):
            print("Krakow days not in 18-22")
            return None
        # Paris 11-15
        paris_days = [entry['day'] for entry in itinerary if entry['place'] == 'Paris']
        if not all(11 <= day <= 15 for day in paris_days):
            print("Paris days not in 11-15")
            return None
        
        return {'itinerary': itinerary}
    else:
        print("No solution found")
        return None

result = solve_itinerary()
if result:
    import json
    print(json.dumps(result, indent=2))