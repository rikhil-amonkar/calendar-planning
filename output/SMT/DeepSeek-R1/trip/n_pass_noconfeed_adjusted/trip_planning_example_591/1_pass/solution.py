from z3 import *
import json

def main():
    s = Solver()
    
    cities = ['Stuttgart', 'Bucharest', 'Geneva', 'Valencia', 'Munich']
    city_index = {c: i for i, c in enumerate(cities)}
    durations = [2, 2, 4, 6, 7]
    
    adj = [
        [3],    # Stuttgart (0) connected to Valencia (3)
        [3,4],  # Bucharest (1) connected to Valencia (3), Munich (4)
        [3,4],  # Geneva (2) connected to Valencia (3), Munich (4)
        [0,1,2,4], # Valencia (3) connected to Stuttgart (0), Bucharest (1), Geneva (2), Munich (4)
        [1,2,3]  # Munich (4) connected to Bucharest (1), Geneva (2), Valencia (3)
    ]
    
    allowed_edges = []
    for u in range(len(adj)):
        for v in adj[u]:
            allowed_edges.append((u, v))
    
    num_segments = 5
    total_days = 17
    
    city_vars = [Int(f'city_{i}') for i in range(num_segments)]
    start_vars = [Int(f'start_{i}') for i in range(num_segments)]
    end_vars = [Int(f'end_{i}') for i in range(num_segments)]
    
    for i in range(num_segments):
        s.add(city_vars[i] >= 0, city_vars[i] <= 4)
    s.add(Distinct(city_vars))
    
    s.add(start_vars[0] == 1)
    s.add(end_vars[num_segments-1] == total_days)
    
    for i in range(num_segments):
        s.add(end_vars[i] - start_vars[i] + 1 == durations[city_vars[i]])
    
    for i in range(num_segments-1):
        s.add(end_vars[i] == start_vars[i+1])
    
    for i in range(num_segments):
        s.add(If(city_vars[i] == city_index['Geneva'], start_vars[i] <= 4, True))
        s.add(If(city_vars[i] == city_index['Munich'], And(start_vars[i] <= 10, end_vars[i] >= 4), True))
    
    for i in range(num_segments-1):
        u = city_vars[i]
        v = city_vars[i+1]
        edge_constraints = []
        for edge in allowed_edges:
            edge_constraints.append(And(u == edge[0], v == edge[1]))
        s.add(Or(edge_constraints))
    
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(num_segments):
            city_val = model.evaluate(city_vars[i]).as_long()
            start_val = model.evaluate(start_vars[i]).as_long()
            end_val = model.evaluate(end_vars[i]).as_long()
            itinerary.append({
                "day_range": f"Day {start_val}-{end_val}",
                "place": cities[city_val]
            })
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == '__main__':
    main()