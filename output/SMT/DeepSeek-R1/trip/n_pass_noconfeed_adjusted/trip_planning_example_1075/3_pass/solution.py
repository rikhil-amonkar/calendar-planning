import z3
import json

def main():
    cities = ['Reykjavik', 'Stuttgart', 'Vienna', 'Edinburgh', 'Manchester', 'Split', 'Lyon', 'Prague']
    required_days = {
        'Reykjavik': 5,
        'Stuttgart': 5,
        'Vienna': 4,
        'Edinburgh': 4,
        'Manchester': 2,
        'Split': 5,
        'Lyon': 3,
        'Prague': 4
    }
    
    connections = [
        ('Reykjavik', 'Stuttgart'),
        ('Stuttgart', 'Split'),
        ('Stuttgart', 'Vienna'),
        ('Prague', 'Manchester'),
        ('Edinburgh', 'Prague'),
        ('Manchester', 'Split'),
        ('Prague', 'Vienna'),
        ('Vienna', 'Manchester'),
        ('Prague', 'Split'),
        ('Vienna', 'Lyon'),
        ('Stuttgart', 'Edinburgh'),
        ('Split', 'Lyon'),
        ('Stuttgart', 'Manchester'),
        ('Prague', 'Lyon'),
        ('Reykjavik', 'Vienna'),
        ('Prague', 'Reykjavik'),
        ('Vienna', 'Split')
    ]
    
    edges = set()
    for conn in connections:
        u, v = conn
        if u > v:
            u, v = v, u
        edges.add((u, v))
    
    non_edges = set()
    for i in range(len(cities)):
        for j in range(i+1, len(cities)):
            city1 = cities[i]
            city2 = cities[j]
            key = (city1, city2) if city1 < city2 else (city2, city1)
            if key not in edges:
                non_edges.add((i, j))
    
    solver = z3.Solver()
    
    s = [z3.Int(f's_{city}') for city in cities]
    e = [z3.Int(f'e_{city}') for city in cities]
    
    for i in range(len(cities)):
        solver.add(s[i] >= 0, e[i] < 25)
        solver.add(e[i] - s[i] + 1 == required_days[cities[i]])
    
    edinburgh_idx = cities.index('Edinburgh')
    solver.add(s[edinburgh_idx] == 4, e[edinburgh_idx] == 7)
    
    split_idx = cities.index('Split')
    solver.add(s[split_idx] <= 22, e[split_idx] >= 18)
    
    for (i, j) in non_edges:
        solver.add(z3.Or(e[i] < s[j], e[j] < s[i]))
    
    for d in range(25):
        count = z3.Sum([z3.If(z3.And(s[i] <= d, d <= e[i]), 1, 0) for i in range(len(cities))])
        if d == 0 or d == 24:
            solver.add(count == 1)
        else:
            solver.add(z3.Or(count == 1, count == 2))
    
    if solver.check() == z3.sat:
        model = solver.model()
        days_per_city = {city: [] for city in cities}
        for i, city in enumerate(cities):
            s_val = model.evaluate(s[i]).as_long()
            e_val = model.evaluate(e[i]).as_long()
            for d in range(s_val, e_val + 1):
                days_per_city[city].append(d+1)
        
        itinerary = []
        for city, days in days_per_city.items():
            days.sort()
            start = days[0]
            current = start
            for i in range(1, len(days)):
                if days[i] != days[i-1] + 1:
                    itinerary.append((start, current, city))
                    start = days[i]
                current = days[i]
            itinerary.append((start, current, city))
        
        itinerary.sort(key=lambda x: x[0])
        result = []
        for start, end, city in itinerary:
            if start == end:
                day_range = f"Day {start}"
            else:
                day_range = f"Day {start}-{end}"
            result.append({"day_range": day_range, "place": city})
        
        print(json.dumps({"itinerary": result}))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()