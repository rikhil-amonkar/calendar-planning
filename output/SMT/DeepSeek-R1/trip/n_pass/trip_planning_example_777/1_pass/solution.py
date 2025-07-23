from z3 import *
import json

def main():
    # Define the days and cities
    n_days = 15
    cities = ['Dublin', 'Helsinki', 'Riga', 'Reykjavik', 'Vienna', 'Tallinn']
    
    # Required days per city
    required_days = {
        'Dublin': 5,
        'Helsinki': 3,
        'Riga': 3,
        'Reykjavik': 2,
        'Vienna': 2,
        'Tallinn': 5
    }
    
    # Define the direct flight connections (undirected)
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
        if a < b:
            edges_set.add((a, b))
        else:
            edges_set.add((b, a))
    
    # Precompute non-edges (pairs of cities without direct flights)
    non_edges = []
    for j in range(len(cities)):
        for k in range(j+1, len(cities)):
            c1 = cities[j]
            c2 = cities[k]
            key = (min(c1, c2), max(c1, c2))
            if key not in edges_set:
                non_edges.append((j, k))
    
    # Create Z3 variables: a 2D list for each day and city
    in_city = [[Bool('day%d_%s' % (i+1, city)) for city in cities] for i in range(n_days)]
    
    # Create a solver
    s = Solver()
    
    # Constraints for each day
    for i in range(n_days):
        # At least one city per day
        s.add(Or(in_city[i]))
        
        # At most two cities per day
        city_bools = [If(b, 1, 0) for b in in_city[i]]
        s.add(Sum(city_bools) <= 2)
        
        # For non-edge pairs, cannot be in both cities on the same day
        for j, k in non_edges:
            s.add(Not(And(in_city[i][j], in_city[i][k])))
    
    # Continuity constraint: consecutive days must share at least one city
    for i in range(n_days - 1):
        s.add(Or([And(in_city[i][j], in_city[i+1][j]) for j in range(len(cities))))
    
    # Total days per city
    for j, city in enumerate(cities):
        total = Sum([If(in_city[i][j], 1, 0) for i in range(n_days)])
        s.add(total == required_days[city])
    
    # Special constraints for events
    helsinki_index = cities.index('Helsinki')
    s.add(Or(in_city[2][helsinki_index], in_city[3][helsinki_index], in_city[4][helsinki_index]))
    
    vienna_index = cities.index('Vienna')
    s.add(Or(in_city[1][vienna_index], in_city[2][vienna_index]))
    
    tallinn_index = cities.index('Tallinn')
    s.add(Or([in_city[i][tallinn_index] for i in range(6, 11)))
    
    # Solve the problem
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(n_days):
            cities_today = []
            for j, city in enumerate(cities):
                if model.evaluate(in_city[i][j]):
                    cities_today.append(city)
            itinerary.append({"day": i+1, "cities": cities_today})
        
        result = {'itinerary': itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()