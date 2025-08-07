from z3 import *
import json

def main():
    cities = [
        'Santorini',
        'Valencia',
        'Madrid',
        'Seville',
        'Bucharest',
        'Vienna',
        'Riga',
        'Tallinn',
        'Krakow',
        'Frankfurt'
    ]
    
    req_days = {
        'Santorini': 3,
        'Valencia': 4,
        'Madrid': 2,
        'Seville': 2,
        'Bucharest': 3,
        'Vienna': 4,
        'Riga': 4,
        'Tallinn': 5,
        'Krakow': 5,
        'Frankfurt': 4
    }
    
    fixed_days = {
        'Madrid': [6, 7],
        'Krakow': [11, 12, 13, 14, 15],
        'Riga': [20, 21, 22, 23],
        'Tallinn': [23, 24, 25, 26, 27]
    }
    
    flight_edges = [
        ('Vienna', 'Bucharest'),
        ('Santorini', 'Madrid'),
        ('Seville', 'Valencia'),
        ('Vienna', 'Seville'),
        ('Vienna', 'Valencia'),
        ('Madrid', 'Valencia'),
        ('Bucharest', 'Riga'),
        ('Valencia', 'Bucharest'),
        ('Santorini', 'Bucharest'),
        ('Valencia', 'Krakow'),
        ('Valencia', 'Frankfurt'),
        ('Krakow', 'Frankfurt'),
        ('Riga', 'Tallinn'),
        ('Vienna', 'Krakow'),
        ('Vienna', 'Frankfurt'),
        ('Madrid', 'Seville'),
        ('Santorini', 'Vienna'),
        ('Vienna', 'Riga'),
        ('Frankfurt', 'Tallinn'),
        ('Frankfurt', 'Bucharest'),
        ('Madrid', 'Bucharest'),
        ('Frankfurt', 'Riga'),
        ('Madrid', 'Frankfurt')
    ]
    
    allowed_pairs = set()
    for u, v in flight_edges:
        key = (min(u, v), max(u, v))
        allowed_pairs.add(key)
    
    in_city = {}
    for city in cities:
        in_city[city] = [Bool(f'in_{city}_{d}') for d in range(1, 28)]
    
    solver = Solver()
    
    for d in range(1, 28):
        day_vars = [in_city[city][d-1] for city in cities]
        solver.add(Or(day_vars))
        solver.add(AtMost(*day_vars, 2))
    
    for city in cities:
        total = 0
        for d in range(1, 28):
            total += If(in_city[city][d-1], 1, 0)
        solver.add(total == req_days[city])
    
    for city, days in fixed_days.items():
        for d in days:
            solver.add(in_city[city][d-1])
    
    vienna_days = in_city['Vienna']
    vienna_blocks = []
    for start in range(1, 25):
        block = []
        for d in range(1, 28):
            if start <= d < start + 4:
                block.append(vienna_days[d-1])
            else:
                block.append(Not(vienna_days[d-1]))
        vienna_blocks.append(And(block))
    solver.add(Or(vienna_blocks))
    
    vienna_in_range = Or(
        vienna_days[2],  # Day 3
        vienna_days[3],  # Day 4
        vienna_days[4],  # Day 5
        vienna_days[5]   # Day 6
    )
    solver.add(vienna_in_range)
    
    for d in range(1, 28):
        for i in range(len(cities)):
            for j in range(i + 1, len(cities)):
                c1 = cities[i]
                c2 = cities[j]
                pair = (min(c1, c2), max(c1, c2))
                if pair not in allowed_pairs:
                    solver.add(Not(And(in_city[c1][d-1], in_city[c2][d-1])))
    
    solver.add(Sum([If(in_city[city][0], 1, 0) for city in cities]) == 1)
    solver.add(Sum([If(in_city[city][26], 1, 0) for city in cities]) == 1)
    
    if solver.check() == sat:
        model = solver.model()
        city_days = {city: [] for city in cities}
        for d in range(1, 28):
            for city in cities:
                if is_true(model.eval(in_city[city][d-1])):
                    city_days[city].append(d)
        
        itinerary = []
        for city in cities:
            days = sorted(city_days[city])
            if not days:
                continue
            start = days[0]
            end = days[0]
            for i in range(1, len(days)):
                if days[i] == end + 1:
                    end = days[i]
                else:
                    itinerary.append({
                        'day_range': f'Day {start}-{end}',
                        'place': city
                    })
                    start = days[i]
                    end = days[i]
            itinerary.append({
                'day_range': f'Day {start}-{end}',
                'place': city
            })
        
        itinerary.sort(key=lambda x: int(x['day_range'].split('-')[0].split()[1]))
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()