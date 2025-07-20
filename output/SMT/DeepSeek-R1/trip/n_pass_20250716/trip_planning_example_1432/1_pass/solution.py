from z3 import *
import json

def main():
    cities = ['Frankfurt', 'Salzburg', 'Athens', 'Reykjavik', 'Bucharest', 'Valencia', 'Vienna', 'Amsterdam', 'Stockholm', 'Riga']
    required_days = {
        'Frankfurt': 4,
        'Salzburg': 5,
        'Athens': 5,
        'Reykjavik': 5,
        'Bucharest': 3,
        'Valencia': 2,
        'Vienna': 5,
        'Amsterdam': 3,
        'Stockholm': 3,
        'Riga': 3
    }
    
    flight_data = [
        "Valencia and Frankfurt", 
        "Vienna and Bucharest", 
        "from Valencia to Athens", 
        "Athens and Bucharest", 
        "Riga and Frankfurt", 
        "Stockholm and Athens", 
        "Amsterdam and Bucharest", 
        "from Athens to Riga", 
        "Amsterdam and Frankfurt", 
        "Stockholm and Vienna", 
        "Vienna and Riga", 
        "Amsterdam and Reykjavik", 
        "Reykjavik and Frankfurt", 
        "Stockholm and Amsterdam", 
        "Amsterdam and Valencia", 
        "Vienna and Frankfurt", 
        "Valencia and Bucharest", 
        "Bucharest and Frankfurt", 
        "Stockholm and Frankfurt", 
        "Valencia and Vienna", 
        "from Reykjavik to Athens", 
        "Frankfurt and Salzburg", 
        "Amsterdam and Vienna", 
        "Stockholm and Reykjavik", 
        "Amsterdam and Riga", 
        "Stockholm and Riga", 
        "Vienna and Reykjavik", 
        "Amsterdam and Athens", 
        "Athens and Frankfurt", 
        "Vienna and Athens", 
        "Riga and Bucharest"
    ]
    
    directed_edges = set()
    for item in flight_data:
        if item.startswith("from "):
            parts = item.split()
            A = parts[1]
            B = parts[3]
            directed_edges.add((A, B))
        else:
            parts = item.split(" and ")
            if len(parts) < 2:
                parts = item.split()
                if len(parts) == 3 and parts[1] == 'and':
                    A = parts[0]
                    B = parts[2]
                else:
                    continue
            else:
                A = parts[0]
                B = parts[1]
            directed_edges.add((A, B))
            directed_edges.add((B, A))
    
    s = {city: Int(f's_{city}') for city in cities}
    e = {city: Int(f'e_{city}') for city in cities}
    n = len(cities)
    p = [[Bool(f'p_{i}_{j}') for j in range(n)] for i in range(n)]
    
    solver = Solver()
    
    for i in range(n):
        solver.add(AtLeast(*p[i], 1))
        solver.add(AtMost(*p[i], 1))
    for j in range(n):
        col = [p[i][j] for i in range(n)]
        solver.add(AtLeast(*col, 1))
        solver.add(AtMost(*col, 1))
    
    for j in range(n):
        solver.add(Implies(p[0][j], s[cities[j]] == 1))
    for j in range(n):
        solver.add(Implies(p[n-1][j], e[cities[j]] == 29))
    
    for i in range(n-1):
        for j in range(n):
            for k in range(n):
                edge_exists = (cities[j], cities[k]) in directed_edges
                solver.add(Implies(And(p[i][j], p[i+1][k]), And(e[cities[j]] == s[cities[k]], edge_exists)))
    
    for city in cities:
        solver.add(e[city] - s[city] + 1 == required_days[city])
        solver.add(s[city] >= 1)
        solver.add(e[city] <= 29)
        solver.add(e[city] >= s[city])
    
    solver.add(s['Valencia'] == 5)
    solver.add(e['Valencia'] == 6)
    solver.add(s['Vienna'] <= 10)
    solver.add(e['Vienna'] >= 6)
    solver.add(s['Athens'] <= 18)
    solver.add(e['Athens'] >= 14)
    solver.add(s['Riga'] <= 20)
    solver.add(e['Riga'] >= 18)
    solver.add(s['Stockholm'] <= 3)
    
    if solver.check() == sat:
        model = solver.model()
        order = []
        for i in range(n):
            for j in range(n):
                if is_true(model[p[i][j]]):
                    order.append(cities[j])
        s_val = {}
        e_val = {}
        for city in cities:
            s_val[city] = model.evaluate(s[city]).as_long()
            e_val[city] = model.evaluate(e[city]).as_long()
        
        itinerary = []
        for idx, city in enumerate(order):
            start = s_val[city]
            end = e_val[city]
            itinerary.append({'day_range': f'Day {start}-{end}', 'place': city})
            if idx < n - 1:
                itinerary.append({'day_range': f'Day {end}', 'place': city})
                next_city = order[idx+1]
                itinerary.append({'day_range': f'Day {end}', 'place': next_city})
        
        result = {'itinerary': itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()