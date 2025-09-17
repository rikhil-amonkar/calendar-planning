import z3
import json

def main():
    # Cities and their codes
    cities = ['F', 'M', 'V', 'N', 'O', 'L']
    city_names = {
        'F': 'Frankfurt',
        'M': 'Manchester',
        'V': 'Valencia',
        'N': 'Naples',
        'O': 'Oslo',
        'L': 'Vilnius'
    }
    
    # Direct flights (unordered pairs)
    direct_flights = [('V','F'), ('M','F'), ('N','M'), ('N','F'), ('N','O'), ('O','F'), ('L','F'), ('O','L'), ('M','O'), ('V','N')]
    connected_set = set()
    for (c1, c2) in direct_flights:
        if c1 > c2:
            c1, c2 = c2, c1
        connected_set.add((c1, c2))
    
    # Initialize solver
    solver = z3.Solver()
    
    # Create variables: for each day and city, a Boolean indicating presence
    in_city = {}
    for day in range(1, 17):
        for city in cities:
            in_city[(day, city)] = z3.Bool(f'in_{day}_{city}')
    
    # Constraint 1: Each day at least one city and at most two cities
    for day in range(1, 17):
        cities_in_day = [in_city[(day, c)] for c in cities]
        solver.add(z3.Or(cities_in_day))
        solver.add(z3.Sum([z3.If(c, 1, 0) for c in cities_in_day]) <= 2)
    
    # Constraint 2: For any two cities not connected by direct flight, they cannot be together on the same day
    for day in range(1, 17):
        for c1 in cities:
            for c2 in cities:
                if c1 < c2:
                    if (c1, c2) not in connected_set:
                        solver.add(z3.Not(z3.And(in_city[(day, c1)], in_city[(day, c2)])))
    
    # Constraint 3: Consecutive days must share at least one common city
    for day in range(1, 16):
        common_cities = []
        for city in cities:
            common_cities.append(z3.And(in_city[(day, city)], in_city[(day+1, city)]))
        solver.add(z3.Or(common_cities))
    
    # Constraint 4: Total days per city
    total_days = {'F': 4, 'M': 4, 'V': 4, 'N': 4, 'O': 3, 'L': 2}
    for city in cities:
        solver.add(z3.Sum([z3.If(in_city[(day, city)], 1, 0) for day in range(1, 17)]) == total_days[city])
    
    # Constraint 5: Fixed constraints
    # Frankfurt from day 13 to 16
    for day in [13, 14, 15, 16]:
        solver.add(in_city[(day, 'F')])
    # Wedding in Vilnius on day 12
    solver.add(in_city[(12, 'L')])
    
    # Solve
    if solver.check() == z3.sat:
        model = solver.model()
        stays = {city: [] for city in cities}
        for day in range(1, 17):
            for city in cities:
                if z3.is_true(model.evaluate(in_city[(day, city)])):
                    stays[city].append(day)
        
        itinerary_entries = []
        for city, days_list in stays.items():
            days_list.sort()
            groups = []
            current = []
            for d in days_list:
                if not current or d == current[-1] + 1:
                    current.append(d)
                else:
                    groups.append(current)
                    current = [d]
            if current:
                groups.append(current)
            for group in groups:
                start = group[0]
                end = group[-1]
                day_range_str = f"Day {start}-{end}" if start != end else f"Day {start}"
                itinerary_entries.append((start, day_range_str, city_names[city]))
        
        itinerary_entries.sort(key=lambda x: x[0])
        itinerary = [{"day_range": e[1], "place": e[2]} for e in itinerary_entries]
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == '__main__':
    main()