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
    
    # Direct flights (bidirectional)
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

    # Create solver
    s = Solver()

    # Day assignments (1-30)
    assignments = [Int(f'd{day}') for day in range(1, 31)]
    for a in assignments:
        s.add(a >= 0, a < len(city_names))

    # City day counts
    for city_idx, city in enumerate(city_names):
        s.add(Sum([If(a == city_idx, 1, 0) for a in assignments]) == city_days[city])

    # Fixed date ranges
    # Santorini days 25-29 (inclusive)
    for day in range(24, 29):  # 0-based days 24-28
        s.add(assignments[day] == city_names.index('Santorini'))
    
    # Krakow days 18-22 (inclusive)
    for day in range(17, 22):  # 0-based days 17-21
        s.add(assignments[day] == city_names.index('Krakow'))
    
    # Paris days 11-15 (inclusive)
    for day in range(10, 15):  # 0-based days 10-14
        s.add(assignments[day] == city_names.index('Paris'))

    # Flight connectivity
    for i in range(29):  # Check transitions between days
        current = assignments[i]
        next_day = assignments[i+1]
        # Allow staying in same city
        s.add(Or(current == next_day, *[
            And(current == city_names.index(c1), next_day == city_names.index(c2))
            for c1 in city_names
            for c2 in direct_flights.get(c1, [])
            if c2 in city_names
        ]))

    # Solve
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for day in range(30):
            city_idx = model[assignments[day]].as_long()
            itinerary.append({"day": day+1, "place": city_names[city_idx]})

        # Verify solution
        day_counts = {city: 0 for city in city_names}
        for entry in itinerary:
            day_counts[entry['place']] += 1

        # Check day counts
        for city in city_names:
            if day_counts[city] != city_days[city]:
                print(f"Day count mismatch for {city}")
                return None

        # Check fixed ranges
        santorini_days = [e['day'] for e in itinerary if e['place'] == 'Santorini']
        if not all(25 <= d <= 29 for d in santorini_days):
            print("Santorini days not in range")
            return None

        krakow_days = [e['day'] for e in itinerary if e['place'] == 'Krakow']
        if not all(18 <= d <= 22 for d in krakow_days):
            print("Krakow days not in range")
            return None

        paris_days = [e['day'] for e in itinerary if e['place'] == 'Paris']
        if not all(11 <= d <= 15 for d in paris_days):
            print("Paris days not in range")
            return None

        # Check flights
        for i in range(29):
            curr = itinerary[i]['place']
            next_p = itinerary[i+1]['place']
            if curr != next_p and next_p not in direct_flights.get(curr, []):
                print(f"Invalid flight from {curr} to {next_p}")
                return None

        return {'itinerary': itinerary}
    else:
        print("No solution found")
        return None

result = solve_itinerary()
if result:
    import json
    print(json.dumps(result, indent=2))