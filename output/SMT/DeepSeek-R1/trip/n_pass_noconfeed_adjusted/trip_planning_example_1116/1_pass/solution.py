from z3 import *
import json

def main():
    n_days = 20
    n_cities = 8
    city_names = ['Oslo', 'Reykjavik', 'Stockholm', 'Munich', 'Frankfurt', 'Barcelona', 'Bucharest', 'Split']
    required_days = [2, 5, 4, 4, 4, 3, 2, 3]
    required_minus_one = [rd - 1 for rd in required_days]
    
    pos = [Int(f'pos_{city}') for city in city_names]
    start = [Int(f'start_{city}') for city in city_names]
    end = [Int(f'end_{city}') for city in city_names]
    
    flight_list = [
        ('Reykjavik', 'Munich'),
        ('Munich', 'Frankfurt'),
        ('Split', 'Oslo'),
        ('Reykjavik', 'Oslo'),
        ('Bucharest', 'Munich'),
        ('Oslo', 'Frankfurt'),
        ('Bucharest', 'Barcelona'),
        ('Barcelona', 'Frankfurt'),
        ('Reykjavik', 'Frankfurt'),
        ('Barcelona', 'Stockholm'),
        ('Barcelona', 'Reykjavik'),
        ('Stockholm', 'Reykjavik'),
        ('Barcelona', 'Split'),
        ('Bucharest', 'Oslo'),
        ('Bucharest', 'Frankfurt'),
        ('Split', 'Stockholm'),
        ('Barcelona', 'Oslo'),
        ('Stockholm', 'Munich'),
        ('Stockholm', 'Oslo'),
        ('Split', 'Frankfurt'),
        ('Barcelona', 'Munich'),
        ('Stockholm', 'Frankfurt'),
        ('Munich', 'Oslo'),
        ('Split', 'Munich')
    ]
    flight_set = set()
    for city1, city2 in flight_list:
        i1 = city_names.index(city1)
        i2 = city_names.index(city2)
        flight_set.add((i1, i2))
        flight_set.add((i2, i1))
    
    s = Solver()
    
    s.add(Distinct(pos))
    for i in range(n_cities):
        s.add(pos[i] >= 0, pos[i] < n_cities)
    
    for i in range(n_cities):
        s.add(start[i] == 1 + Sum([If(pos[j] < pos[i], required_minus_one[j], 0) for j in range(n_cities)]))
        s.add(end[i] == start[i] + required_days[i] - 1)
    
    for i in range(n_cities):
        s.add(If(pos[i] == 7, end[i] == 20, True))
    
    oslo_idx = city_names.index('Oslo')
    s.add(start[oslo_idx] <= 16)
    s.add(end[oslo_idx] >= 17)
    
    reykjavik_idx = city_names.index('Reykjavik')
    s.add(start[reykjavik_idx] <= 13)
    s.add(end[reykjavik_idx] >= 9)
    
    munich_idx = city_names.index('Munich')
    s.add(start[munich_idx] <= 16)
    s.add(end[munich_idx] >= 13)
    
    frankfurt_idx = city_names.index('Frankfurt')
    s.add(start[frankfurt_idx] <= 20)
    s.add(end[frankfurt_idx] >= 17)
    
    for i in range(n_cities):
        for j in range(n_cities):
            s.add(If(pos[j] == pos[i] + 1, Or([And(i == a, j == b) for (a, b) in flight_set]), True))
    
    if s.check() == sat:
        m = s.model()
        start_vals = [m.evaluate(s).as_long() for s in start]
        end_vals = [m.evaluate(e).as_long() for e in end]
        segments = []
        for i in range(n_cities):
            segments.append((start_vals[i], end_vals[i], city_names[i]))
        segments.sort(key=lambda x: x[0])
        itinerary = []
        for seg in segments:
            s, e, city = seg
            itinerary.append({"day_range": f"Day {s}-{e}", "place": city})
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()