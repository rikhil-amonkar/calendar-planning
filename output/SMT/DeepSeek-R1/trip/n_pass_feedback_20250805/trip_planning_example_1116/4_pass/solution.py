from z3 import *
import json

def main():
    cities = ['Oslo', 'Reykjavik', 'Stockholm', 'Munich', 'Frankfurt', 'Barcelona', 'Bucharest', 'Split']
    city_index = {city: idx for idx, city in enumerate(cities)}
    required_days = {
        'Oslo': 2,
        'Reykjavik': 5,
        'Stockholm': 4,
        'Munich': 4,
        'Frankfurt': 4,
        'Barcelona': 3,
        'Bucharest': 2,
        'Split': 3
    }
    required_days_list = [required_days[city] for city in cities]
    
    connections_list = [
        "Reykjavik and Munich", "Munich and Frankfurt", "Split and Oslo", "Reykjavik and Oslo", 
        "Bucharest and Munich", "Oslo and Frankfurt", "Bucharest and Barcelona", "Barcelona and Frankfurt", 
        "Reykjavik and Frankfurt", "Barcelona and Stockholm", "Barcelona and Reykjavik", "Stockholm and Reykjavik", 
        "Barcelona and Split", "Bucharest and Oslo", "Bucharest and Frankfurt", "Split and Stockholm", 
        "Barcelona and Oslo", "Stockholm and Munich", "Stockholm and Oslo", "Split and Frankfurt", 
        "Barcelona and Munich", "Stockholm and Frankfurt", "Munich and Oslo", "Split and Munich"
    ]
    
    connected_pairs_index = set()
    for conn in connections_list:
        a, b = conn.split(' and ')
        a = a.strip()
        b = b.strip()
        i = city_index[a]
        j = city_index[b]
        if i < j:
            pair = (i, j)
        else:
            pair = (j, i)
        connected_pairs_index.add(pair)
    
    all_pairs = set()
    for i in range(8):
        for j in range(i+1, 8):
            all_pairs.add((i, j))
    
    non_connected_pairs = all_pairs - connected_pairs_index

    X = [[Bool(f'x_day_{d}_city_{c}') for c in range(8)] for d in range(20)]
    start_c = [Int(f'start_{i}') for i in range(8)]
    end_c = [Int(f'end_{i}') for i in range(8)]
    
    s = Solver()
    
    for i in range(8):
        s.add(start_c[i] >= 1)
        s.add(start_c[i] <= 20)
        s.add(end_c[i] >= 1)
        s.add(end_c[i] <= 20)
        s.add(end_c[i] - start_c[i] + 1 == required_days_list[i])
        
    for d in range(20):
        for i in range(8):
            s.add(X[d][i] == And(d+1 >= start_c[i], d+1 <= end_c[i]))
    
    for d in range(20):
        total_cities = Sum([If(X[d][c], 1, 0) for c in range(8)])
        s.add(Or(total_cities == 1, total_cities == 2))
    
    for d in range(20):
        for (i, j) in non_connected_pairs:
            s.add(Not(And(X[d][i], X[d][j])))
    
    for d in range(19):
        s.add(Or([And(X[d][c], X[d+1][c]) for c in range(8)]))
    
    s.add(Or([And(X[15][city_index['Oslo']], X[16][city_index['Oslo']])]))
    s.add(Or([X[d][city_index['Reykjavik']] for d in range(8, 13)]))
    s.add(Or([X[d][city_index['Munich']] for d in range(12, 16)]))
    s.add(Or([X[d][city_index['Frankfurt']] for d in range(16, 20)]))
    
    double_days = [If(Sum([If(X[d][c], 1, 0) for c in range(8)]) == 2, 1, 0) for d in range(20)]
    s.add(Sum(double_days) == 7)
    
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for d in range(20):
            for c_idx, city in enumerate(cities):
                if is_true(m.evaluate(X[d][c_idx])):
                    itinerary.append({"day": d+1, "place": city})
        result = {'itinerary': itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()