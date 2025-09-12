import json
from z3 import *

def main():
    # Define cities and their indices
    cities = ['Stuttgart', 'Edinburgh', 'Athens', 'Split', 'Krakow', 'Venice', 'Mykonos']
    city_index = {city: idx for idx, city in enumerate(cities)}
    n_days = 20
    n_cities = len(cities)

    # Required days per city
    required_days = {
        'Stuttgart': 3,
        'Edinburgh': 4,
        'Athens': 4,
        'Split': 2,
        'Krakow': 4,
        'Venice': 5,
        'Mykonos': 4
    }

    # Direct flights (as city index pairs)
    flight_pairs = [
        ('Krakow', 'Split'),
        ('Split', 'Athens'),
        ('Edinburgh', 'Krakow'),
        ('Venice', 'Stuttgart'),
        ('Krakow', 'Stuttgart'),
        ('Edinburgh', 'Stuttgart'),
        ('Stuttgart', 'Athens'),
        ('Venice', 'Edinburgh'),
        ('Athens', 'Mykonos'),
        ('Venice', 'Athens'),
        ('Stuttgart', 'Split'),
        ('Edinburgh', 'Athens')
    ]
    allowed_pairs = set()
    for city1, city2 in flight_pairs:
        idx1 = city_index[city1]
        idx2 = city_index[city2]
        allowed_pairs.add((idx1, idx2))
        allowed_pairs.add((idx2, idx1))

    # Create Z3 solver
    solver = Solver()

    # Create a grid of Booleans: days x cities
    in_city = [[Bool(f"day_{i}_city_{c}") for c in range(n_cities)] for i in range(n_days)]

    # Constraint: Each day must have at least one city and at most two cities
    for i in range(n_days):
        solver.add(Or([in_city[i][c] for c in range(n_cities)]))
        for c1 in range(n_cities):
            for c2 in range(c1+1, n_cities):
                for c3 in range(c2+1, n_cities):
                    solver.add(Not(And(in_city[i][c1], in_city[i][c2], in_city[i][c3])))

    # Constraint: Total days per city must match requirements
    for c, city in enumerate(cities):
        total_days = Sum([If(in_city[i][c], 1, 0) for i in range(n_days)])
        solver.add(total_days == required_days[city])

    # Constraint: Consecutive days must share at least one city
    for i in range(n_days-1):
        solver.add(Or([And(in_city[i][c], in_city[i+1][c]) for c in range(n_cities)]))

    # Constraint: If two cities on same day, they must be connected by direct flight
    bad_pairs = set()
    for c1 in range(n_cities):
        for c2 in range(n_cities):
            if c1 != c2 and (c1, c2) not in allowed_pairs:
                bad_pairs.add((c1, c2))
    for i in range(n_days):
        for (c1, c2) in bad_pairs:
            solver.add(Not(And(in_city[i][c1], in_city[i][c2])))

    # Specific constraints
    # Stuttgart must be present on days 11,12,13 (indexed 10,11,12)
    for i in [10, 11, 12]:
        solver.add(in_city[i][city_index['Stuttgart']])
    # Split must be present on day 13 or 14 (indexed 12 or 13)
    solver.add(Or(in_city[12][city_index['Split']], in_city[13][city_index['Split']]))
    # Krakow must be present between day 8 and 11 (indexed 7 to 10)
    solver.add(Or([in_city[i][city_index['Krakow']] for i in range(7, 11)]))

    # Check feasibility
    if solver.check() == sat:
        model = solver.model()
        # Extract the presence matrix
        schedule = []
        for i in range(n_days):
            day_cities = []
            for c in range(n_cities):
                if is_true(model.eval(in_city[i][c])):
                    day_cities.append(cities[c])
            schedule.append(day_cities)
        
        # Create segments for output
        segments = []
        for c, city in enumerate(cities):
            days_present = []
            for i in range(n_days):
                if is_true(model.eval(in_city[i][c])):
                    days_present.append(i+1)  # 1-indexed days
            # Group consecutive days
            if days_present:
                start = days_present[0]
                current = start
                for day in days_present[1:]:
                    if day == current + 1:
                        current = day
                    else:
                        segments.append({
                            'start': start,
                            'end': current,
                            'place': city
                        })
                        start = day
                        current = day
                segments.append({
                    'start': start,
                    'end': current,
                    'place': city
                })
        
        # Sort segments by start day
        segments.sort(key=lambda x: x['start'])
        
        # Format output
        itinerary = []
        for seg in segments:
            if seg['start'] == seg['end']:
                day_range = f"Day {seg['start']}"
            else:
                day_range = f"Day {seg['start']}-{seg['end']}"
            itinerary.append({
                'day_range': day_range,
                'place': seg['place']
            })
        
        result = {'itinerary': itinerary}
        print(json.dumps(result, indent=2))
    else:
        print('{"itinerary": []}')

if __name__ == '__main__':
    main()