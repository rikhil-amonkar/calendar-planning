from z3 import *

def solve_itinerary():
    # Cities
    cities = {
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
    
    city_list = list(cities.keys())
    city_vars = {city: [Bool(f"{city}_{day}") for day in range(1, 31)] for city in city_list}
    
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
    
    s = Solver()
    
    # Each day is exactly one city
    for day in range(1, 31):
        s.add(Or([city_vars[city][day-1] for city in city_list]))
        for city1 in city_list:
            for city2 in city_list:
                if city1 != city2:
                    s.add(Not(And(city_vars[city1][day-1], city_vars[city2][day-1])))
    
    # Total days per city
    for city in city_list:
        s.add(Sum([If(city_vars[city][day], 1, 0) for day in range(30)]) == cities[city])
    
    # Specific date ranges
    # Santorini between day 25-29 (inclusive)
    for day in range(25, 30):
        s.add(city_vars['Santorini'][day-1])
    
    # Krakow between day 18-22
    for day in range(18, 23):
        s.add(city_vars['Krakow'][day-1])
    
    # Paris between day 11-15
    for day in range(11, 16):
        s.add(city_vars['Paris'][day-1])
    
    # Flight transitions: if day i is city A and day i+1 is city B, then there's a direct flight
    for day in range(1, 30):
        for city1 in city_list:
            for city2 in city_list:
                if city1 != city2:
                    # Check if there's a direct flight
                    if city2 not in direct_flights.get(city1, []):
                        s.add(Not(And(city_vars[city1][day-1], city_vars[city2][day])))
    
    # Check model
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for day in range(1, 31):
            for city in city_list:
                if is_true(model[city_vars[city][day-1]]):
                    itinerary.append({"day": day, "place": city})
                    break
        # Verify transitions
        valid = True
        for i in range(len(itinerary) - 1):
            current_city = itinerary[i]['place']
            next_city = itinerary[i+1]['place']
            if current_city != next_city and next_city not in direct_flights[current_city]:
                valid = False
                break
        if not valid:
            print("Invalid transitions found.")
            return None
        # Verify day counts
        day_counts = {city: 0 for city in city_list}
        for entry in itinerary:
            day_counts[entry['place']] += 1
        for city in city_list:
            if day_counts[city] != cities[city]:
                print(f"Day count mismatch for {city}: expected {cities[city]}, got {day_counts[city]}")
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