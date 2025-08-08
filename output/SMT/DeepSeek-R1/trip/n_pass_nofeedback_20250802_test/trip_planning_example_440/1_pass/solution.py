from z3 import *

def main():
    # City indices for easier reference
    cities = {
        'Split': 0,
        'Helsinki': 1,
        'Reykjavik': 2,
        'Vilnius': 3,
        'Geneva': 4
    }
    city_names = ['Split', 'Helsinki', 'Reykjavik', 'Vilnius', 'Geneva']
    n_cities = len(city_names)
    n_days = 12

    # Direct flights as a set of tuples (unordered)
    direct_flights = {
        ('Split', 'Helsinki'),
        ('Geneva', 'Split'),
        ('Geneva', 'Helsinki'),
        ('Helsinki', 'Reykjavik'),
        ('Vilnius', 'Helsinki'),
        ('Split', 'Vilnius')
    }

    # Create a solver instance
    s = Solver()

    # in_city[day][city]: True if we are in the city on that day
    in_city = [[Bool(f'in_city_{d}_{c}') for c in range(n_cities)] for d in range(n_days)]

    # Constraint: Each day, we are in at least one city and at most two cities.
    for d in range(n_days):
        # At least one city per day
        s.add(Or([in_city[d][c] for c in range(n_cities)]))
        # At most two cities: for any three distinct cities, not all can be true on the same day.
        for c1 in range(n_cities):
            for c2 in range(c1 + 1, n_cities):
                for c3 in range(c2 + 1, n_cities):
                    s.add(Not(And(in_city[d][c1], in_city[d][c2], in_city[d][c3])))

    # Constraint: If two cities are occupied on the same day, they must be connected by a direct flight.
    for d in range(n_days):
        for c1 in range(n_cities):
            for c2 in range(c1 + 1, n_cities):
                city1 = city_names[c1]
                city2 = city_names[c2]
                if (city1, city2) not in direct_flights and (city2, city1) not in direct_flights:
                    # If no direct flight, they cannot be together on the same day.
                    s.add(Not(And(in_city[d][c1], in_city[d][c2])))

    # Constraint: Total days per city must meet the requirements.
    total_days = [0] * n_cities
    for c in range(n_cities):
        total = 0
        for d in range(n_days):
            total += If(in_city[d][c], 1, 0)
        if city_names[c] == 'Split':
            s.add(total == 2)
        elif city_names[c] == 'Helsinki':
            s.add(total == 2)
        elif city_names[c] == 'Reykjavik':
            s.add(total == 3)
        elif city_names[c] == 'Vilnius':
            s.add(total == 3)
        elif city_names[c] == 'Geneva':
            s.add(total == 6)

    # Reykjavik must be occupied on days 10, 11, 12 (which are indices 9,10,11)
    s.add(in_city[9][cities['Reykjavik']])
    s.add(in_city[10][cities['Reykjavik']])
    s.add(in_city[11][cities['Reykjavik']])

    # Vilnius must be occupied on at least one day between 7 and 9 (indices 6,7,8)
    s.add(Or(
        in_city[6][cities['Vilnius']],
        in_city[7][cities['Vilnius']],
        in_city[8][cities['Vilnius']]
    ))

    # Check and get the model
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for d in range(n_days):
            current_cities = []
            for c in range(n_cities):
                if model.evaluate(in_city[d][c]):
                    current_cities.append(city_names[c])
            itinerary.append({"day": d + 1, "place": ", ".join(current_cities)})
        
        # Output the itinerary in the required JSON format
        import json
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()