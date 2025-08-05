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
        ('Madrid', 'Valencia'),
        ('Bucharest', 'Riga'),
        ('Valencia', 'Bucharest'),
        ('Santorini', 'Bucharest'),
        ('Vienna', 'Valencia'),
        ('Vienna', 'Madrid'),
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
    
    edges_set = set()
    for edge in flight_edges:
        u, v = edge
        key = (min(u, v), max(u, v))
        edges_set.add(key)
    
    in_city = {}
    for city in cities:
        in_city[city] = [Bool(f'in_{city}_{d}') for d in range(1, 28)]
    
    solver = Solver()
    
    for d in range(1, 28):
        day_vars = [in_city[city][d-1] for city in cities]
        solver.add(Or(day_vars))
        
        for i in range(len(cities)):
            for j in range(i+1, len(cities)):
                for k in range(j+1, len(cities)):
                    c1, c2, c3 = cities[i], cities[j], cities[k]
                    solver.add(Not(And(in_city[c1][d-1], in_city[c2][d-1], in_city[c3][d-1])))
    
    for city in cities:
        total = 0
        for d in range(1, 28):
            total += If(in_city[city][d-1], 1, 0)
        solver.add(total == req_days[city])
    
    for d in range(1, 27):
        common_city = Or([And(in_city[city][d-1], in_city[city][d]) for city in cities])
        solver.add(common_city)
    
    for d in range(1, 28):
        for i in range(len(cities)):
            for j in range(i+1, len(cities)):
                c1 = cities[i]
                c2 = cities[j]
                key = (min(c1, c2), max(c1, c2))
                if key not in edges_set:
                    solver.add(Not(And(in_city[c1][d-1], in_city[c2][d-1])))
    
    for city, days in fixed_days.items():
        for d in days:
            solver.add(in_city[city][d-1])
    
    vienna_days = [in_city['Vienna'][d] for d in range(27)]
    consecutive_vienna = []
    for start in range(0, 24):
        consecutive_vienna.append(And([vienna_days[start + i] for i in range(4)]))
    solver.add(Or(consecutive_vienna))
    solver.add(Or([in_city['Vienna'][2], in_city['Vienna'][3], in_city['Vienna'][4], in_city['Vienna'][5]]))
    
    solver.add(And(in_city['Vienna'][5], in_city['Madrid'][5]))
    solver.add(And(in_city['Riga'][22], in_city['Tallinn'][22]))
    
    first_day_sum = Sum([If(in_city[city][0], 1, 0) for city in cities])
    solver.add(first_day_sum == 1)
    
    last_day_sum = Sum([If(in_city[city][26], 1, 0) for city in cities])
    solver.add(last_day_sum == 1)
    
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for d in range(1, 28):
            for city in cities:
                if is_true(model.eval(in_city[city][d-1])):
                    itinerary.append({"day": d, "city": city})
        
        output = {"itinerary": itinerary}
        print(json.dumps(output, indent=2))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()