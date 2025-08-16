import z3
import json

def main():
    solver = z3.Solver()

    # Define cities as 0-7
    cities_order = [z3.Int(f'city_{i}') for i in range(8)]

    # All cities are distinct and between 0 and 7
    for city in cities_order:
        solver.add(z3.And(city >= 0, city <= 7))
    solver.add(z3.Distinct(cities_order))

    # Allowed flights
    allowed_flights = {
        (1, 3), (3, 1),
        (3, 4), (4, 3),
        (7, 0), (0, 7),
        (1, 0), (0, 1),
        (6, 3), (3, 6),
        (0, 4), (4, 0),
        (6, 5), (5, 6),
        (5, 4), (4, 5),
        (1, 4), (4, 1),
        (5, 2), (2, 5),
        (5, 1), (1, 5),
        (2, 1), (1, 2),
        (5, 7), (7, 5),
        (6, 0), (0, 6),
        (6, 4), (4, 6),
        (7, 2), (2, 7),
        (5, 0), (0, 5),
        (2, 0), (0, 2),
        (7, 4), (4, 7),
        (5, 3), (3, 5),
        (2, 4), (4, 2),
        (3, 0), (0, 3),
        (7, 3), (3, 7),
    }

    # Add constraints for consecutive flights
    for i in range(7):
        current = cities_order[i]
        next_city = cities_order[i+1]
        allowed_conditions = []
        for a, b in allowed_flights:
            allowed_conditions.append(z3.And(current == a, next_city == b))
        solver.add(z3.Or(allowed_conditions))

    # Define durations for each city
    durations = {
        0: 2,   # Oslo
        1: 5,   # Reykjavik
        2: 4,   # Stockholm
        3: 4,   # Munich
        4: 4,   # Frankfurt
        5: 3,   # Barcelona
        6: 2,   # Bucharest
        7: 3,   # Split
    }

    # Define start_days variables
    start_days = [z3.Int(f'start_{i}') for i in range(8)]

    # Constraints for start_days
    solver.add(start_days[0] == 1)
    for i in range(7):
        solver.add(start_days[i+1] == start_days[i] + durations[cities_order[i]] - 1)
    # Last day must be 20
    solver.add(start_days[7] + durations[cities_order[7]] - 1 == 20)

    # Add time constraints for specific cities
    for i in range(8):
        city = cities_order[i]
        # Oslo (0) must start on day 16
        solver.add(z3.Implies(city == 0, start_days[i] == 16))
        # Reykjavik (1) must start between 5 and 13
        solver.add(z3.Implies(city == 1, z3.And(start_days[i] >= 5, start_days[i] <= 13)))
        # Munich (3) must start between 10 and 16
        solver.add(z3.Implies(city == 3, z3.And(start_days[i] >= 10, start_days[i] <= 16)))
        # Frankfurt (4) must start on day 17
        solver.add(z3.Implies(city == 4, start_days[i] == 17))

    # Check if the solver can find a solution
    if solver.check() == z3.sat:
        model = solver.model()
        # Extract cities_order and start_days
        cities_order_values = [model.eval(c).as_long() for c in cities_order]
        start_days_values = [model.eval(s).as_long() for s in start_days]

        # Generate the itinerary
        itinerary = []
        for idx in range(8):
            city_idx = cities_order_values[idx]
            duration = durations[city_idx]
            start = start_days_values[idx]
            city_name = {
                0: 'Oslo',
                1: 'Reykjavik',
                2: 'Stockholm',
                3: 'Munich',
                4: 'Frankfurt',
                5: 'Barcelona',
                6: 'Bucharest',
                7: 'Split',
            }[city_idx]
            for day in range(start, start + duration):
                itinerary.append({'day': day, 'city': city_name})

        # Sort itinerary by day (though it should already be in order)
        itinerary.sort(key=lambda x: x['day'])

        # Format as JSON
        result = {
            'itinerary': [{'day': entry['day'], 'city': entry['city']} for entry in itinerary]
        }
        print(json.dumps(result, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()