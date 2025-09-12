import json
from z3 import *

def main():
    # Define cities and days
    cities = ['Stuttgart', 'Istanbul', 'Vilnius', 'Seville', 'Geneva', 'Valencia', 'Munich', 'Reykjavik']
    city_dict = {city: idx for idx, city in enumerate(cities)}
    n_days = 25
    n_cities = len(cities)
    
    # Direct flights (symmetric)
    flights = [
        ('Geneva', 'Istanbul'),
        ('Reykjavik', 'Munich'),
        ('Stuttgart', 'Valencia'),
        ('Reykjavik', 'Stuttgart'),
        ('Stuttgart', 'Istanbul'),
        ('Munich', 'Geneva'),
        ('Istanbul', 'Vilnius'),
        ('Valencia', 'Seville'),
        ('Valencia', 'Istanbul'),
        ('Vilnius', 'Munich'),
        ('Seville', 'Munich'),
        ('Munich', 'Istanbul'),
        ('Valencia', 'Geneva'),
        ('Valencia', 'Munich')
    ]
    
    # Convert city names to indices in flight pairs
    flight_pairs = set()
    for a, b in flights:
        i = city_dict[a]
        j = city_dict[b]
        flight_pairs.add((i, j))
        flight_pairs.add((j, i))
    
    # Create solver
    solver = Solver()
    
    # Variables: in_city[day][city] = Bool
    in_city = [[Bool(f"day_{day}_city_{city}") for city in range(n_cities)] for day in range(n_days)]
    
    # Constraints for each day
    for day in range(n_days):
        # At least one city per day
        solver.add(Or([in_city[day][c] for c in range(n_cities)]))
        # At most two cities per day
        for c1 in range(n_cities):
            for c2 in range(c1+1, n_cities):
                for c3 in range(c2+1, n_cities):
                    solver.add(Not(And(in_city[day][c1], in_city[day][c2], in_city[day][c3])))
    
    # Travel constraint: if two cities on same day, must have direct flight
    for day in range(n_days):
        for c1 in range(n_cities):
            for c2 in range(c1+1, n_cities):
                if (c1, c2) not in flight_pairs:
                    solver.add(Not(And(in_city[day][c1], in_city[day][c2])))
    
    # Consecutive day constraint: consecutive days must share at least one city
    for day in range(n_days-1):
        solver.add(Or([And(in_city[day][c], in_city[day+1][c]) for c in range(n_cities)]))
    
    # Fixed events
    # Reykjavik days 1-4 (index 0-3)
    for day in range(4):
        solver.add(in_city[day][city_dict['Reykjavik']])
    # Stuttgart day 4 (index 3) and day 7 (index 6)
    solver.add(in_city[3][city_dict['Stuttgart']])
    solver.add(in_city[6][city_dict['Stuttgart']])
    # Munich days 13-15 (index 12-14)
    for day in range(12, 15):
        solver.add(in_city[day][city_dict['Munich']])
    # Istanbul days 19-22 (index 18-21)
    for day in range(18, 22):
        solver.add(in_city[day][city_dict['Istanbul']])
    
    # Total days per city
    total_days = {
        'Stuttgart': 4,
        'Istanbul': 4,
        'Vilnius': 4,
        'Seville': 3,
        'Geneva': 5,
        'Valencia': 5,
        'Munich': 3,
        'Reykjavik': 4
    }
    for city, total in total_days.items():
        c_index = city_dict[city]
        solver.add(Sum([If(in_city[day][c_index], 1, 0) for day in range(n_days)]) == total)
    
    # Check and get model
    if solver.check() == sat:
        model = solver.model()
        # Decode the model
        itinerary = []
        current_places = None
        start_day = 0
        for day in range(n_days):
            places = []
            for c in range(n_cities):
                if is_true(model.eval(in_city[day][c])):
                    places.append(cities[c])
            places_str = ', '.join(sorted(places))
            if day == 0:
                current_places = places_str
                continue
            if places_str != current_places:
                end_day = day
                itinerary.append({
                    "day_range": f"Day {start_day+1}-{end_day}",
                    "place": current_places
                })
                start_day = day
                current_places = places_str
        itinerary.append({
            "day_range": f"Day {start_day+1}-{n_days}",
            "place": current_places
        })
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == '__main__':
    main()