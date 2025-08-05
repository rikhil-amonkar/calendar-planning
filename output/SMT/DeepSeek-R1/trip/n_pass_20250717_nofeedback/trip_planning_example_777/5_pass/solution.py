from z3 import *
import json

def main():
    n_days = 15
    cities = ['Dublin', 'Helsinki', 'Riga', 'Reykjavik', 'Vienna', 'Tallinn']
    
    required_days = {
        'Dublin': 5,
        'Helsinki': 3,
        'Riga': 3,
        'Reykjavik': 2,
        'Vienna': 2,
        'Tallinn': 5
    }
    
    edges_list = [
        ('Helsinki', 'Riga'),
        ('Riga', 'Tallinn'),
        ('Vienna', 'Helsinki'),
        ('Riga', 'Dublin'),
        ('Vienna', 'Riga'),
        ('Reykjavik', 'Vienna'),
        ('Helsinki', 'Dublin'),
        ('Tallinn', 'Dublin'),
        ('Reykjavik', 'Helsinki'),
        ('Reykjavik', 'Dublin'),
        ('Helsinki', 'Tallinn'),
        ('Vienna', 'Dublin')
    ]
    
    edges_set = set()
    for a, b in edges_list:
        key = (min(a, b), max(a, b))
        edges_set.add(key)
    
    non_edges = []
    for j in range(len(cities)):
        for k in range(j + 1, len(cities)):
            c1 = cities[j]
            c2 = cities[k]
            key = (min(c1, c2), max(c1, c2))
            if key not in edges_set:
                non_edges.append((j, k))
    
    in_city = [[Bool(f'day{i+1}_{city}') for city in cities] for i in range(n_days)]
    
    s = Solver()
    
    # Block problematic transition from first invalid solution
    vienna_idx = cities.index('Vienna')
    reykjavik_idx = cities.index('Reykjavik')
    other_cities_day0 = [in_city[0][j] for j in range(len(cities)) if j != vienna_idx]
    s.add(Not(And(
        in_city[0][vienna_idx],
        Not(Or(other_cities_day0)),
        in_city[1][reykjavik_idx],
        in_city[1][vienna_idx]
    )))
    
    for i in range(n_days):
        # At least one city per day
        s.add(Or(in_city[i]))
        
        # At most two cities per day
        expr = [If(b, 1, 0) for b in in_city[i]]
        s.add(Sum(expr) <= 2)
        
        # Enforce flight connections
        for j, k in non_edges:
            s.add(Not(And(in_city[i][j], in_city[i][k])))
    
    # Ensure consecutive days share at least one city
    for i in range(n_days - 1):
        common_city = Or([And(in_city[i][j], in_city[i+1][j]) for j in range(len(cities))])
        s.add(common_city)
    
    # Ensure required days per city
    for j in range(len(cities)):
        total_days = Sum([If(in_city[i][j], 1, 0) for i in range(n_days)])
        s.add(total_days == required_days[cities[j]])
    
    # Special event constraints
    helsinki_idx = cities.index('Helsinki')
    vienna_idx = cities.index('Vienna')
    tallinn_idx = cities.index('Tallinn')
    
    # Helsinki between days 3-5 (inclusive)
    s.add(Or(in_city[2][helsinki_idx], in_city[3][helsinki_idx], in_city[4][helsinki_idx]))
    
    # Vienna between days 2-3 (inclusive)
    s.add(Or(in_city[1][vienna_idx], in_city[2][vienna_idx]))
    
    # Tallinn between days 7-11 (inclusive)
    s.add(Or([in_city[i][tallinn_idx] for i in range(6, 11)]))
    
    # Solve and output
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(n_days):
            cities_today = []
            for j, city in enumerate(cities):
                if is_true(model.evaluate(in_city[i][j])):
                    cities_today.append(city)
            itinerary.append({"day": i + 1, "cities": cities_today})
        result = {'itinerary': itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()