from z3 import *
import json

def main():
    cities = ['London', 'Milan', 'Zurich', 'Reykjavik', 'Bucharest', 'Hamburg', 'Barcelona', 'Stuttgart', 'Stockholm', 'Tallinn']
    n_cities = len(cities)
    required_days = {
        'London': 3,
        'Milan': 5,
        'Zurich': 2,
        'Reykjavik': 5,
        'Bucharest': 2,
        'Hamburg': 5,
        'Barcelona': 4,
        'Stuttgart': 5,
        'Stockholm': 2,
        'Tallinn': 4
    }
    
    edges_list = [
        ('London', 'Hamburg'),
        ('London', 'Reykjavik'),
        ('Milan', 'Barcelona'),
        ('Reykjavik', 'Barcelona'),
        ('Reykjavik', 'Stuttgart'),
        ('Stockholm', 'Reykjavik'),
        ('London', 'Stuttgart'),
        ('Milan', 'Zurich'),
        ('London', 'Barcelona'),
        ('Stockholm', 'Hamburg'),
        ('Zurich', 'Barcelona'),
        ('Stockholm', 'Stuttgart'),
        ('Milan', 'Hamburg'),
        ('Stockholm', 'Tallinn'),
        ('Hamburg', 'Bucharest'),
        ('London', 'Bucharest'),
        ('Milan', 'Stockholm'),
        ('Stuttgart', 'Hamburg'),
        ('London', 'Zurich'),
        ('Milan', 'Reykjavik'),
        ('London', 'Stockholm'),
        ('Milan', 'Stuttgart'),
        ('Stockholm', 'Barcelona'),
        ('London', 'Milan'),
        ('Zurich', 'Hamburg'),
        ('Bucharest', 'Barcelona'),
        ('Zurich', 'Stockholm'),
        ('Barcelona', 'Tallinn'),
        ('Zurich', 'Tallinn'),
        ('Hamburg', 'Barcelona'),
        ('Stuttgart', 'Barcelona'),
        ('Zurich', 'Reykjavik'),
        ('Zurich', 'Bucharest')
    ]
    
    allowed_edges_set = set()
    for c1, c2 in edges_list:
        idx1 = cities.index(c1)
        idx2 = cities.index(c2)
        edge_tuple = (min(idx1, idx2), max(idx1, idx2))
        allowed_edges_set.add(edge_tuple)
    
    L = [Int(f'L_{i}') for i in range(29)]
    s = Solver()
    
    s.add(L[0] == 0)
    
    for i in range(29):
        s.add(L[i] >= 0, L[i] < n_cities)
    
    for i in range(1, 29):
        cond = Or(L[i-1] == L[i])
        for (a, b) in allowed_edges_set:
            cond = Or(cond, And(L[i-1] == a, L[i] == b), And(L[i-1] == b, L[i] == a))
        s.add(cond)
    
    for c in range(n_cities):
        total = 0
        for i in range(1, 29):
            total += If(Or(L[i-1] == c, L[i] == c), 1, 0)
        s.add(total == required_days[cities[c]])
    
    s.add(Or(L[1] == 0, L[2] == 0))
    s.add(Or(L[2] == 0, L[3] == 0))
    
    s.add(Or(L[2] == 1, L[3] == 1))
    s.add(Or(L[3] == 1, L[4] == 1))
    s.add(Or(L[4] == 1, L[5] == 1))
    s.add(Or(L[5] == 1, L[6] == 1))
    s.add(Or(L[6] == 1, L[7] == 1))
    
    s.add(Or(L[6] == 2, L[7] == 2))
    s.add(Or(L[7] == 2, L[8] == 2))
    
    s.add(Or(L[8] == 3, L[9] == 3))
    s.add(Or(L[9] == 3, L[10] == 3))
    s.add(Or(L[10] == 3, L[11] == 3))
    s.add(Or(L[11] == 3, L[12] == 3))
    s.add(Or(L[12] == 3, L[13] == 3))
    
    if s.check() == sat:
        m = s.model()
        tour = [m.evaluate(L[i]) for i in range(29)]
        itinerary = []
        for day in range(1, 29):
            idx1 = tour[day-1].as_long()
            idx2 = tour[day].as_long()
            cities_day = set()
            cities_day.add(cities[idx1])
            if idx1 != idx2:
                cities_day.add(cities[idx2])
            for city in cities_day:
                itinerary.append({"day": day, "city": city})
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()