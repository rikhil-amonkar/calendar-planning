from z3 import *
import json

def main():
    cities = ["Prague", "Tallinn", "Warsaw", "Porto", "Naples", "Milan", "Lisbon", "Santorini", "Riga", "Stockholm"]
    lengths = [5, 3, 2, 3, 5, 3, 5, 5, 4, 2]
    city_index = {city: idx for idx, city in enumerate(cities)}
    
    flight_connections = [
        "Riga and Prague", 
        "Stockholm and Milan", 
        "Riga and Milan", 
        "Lisbon and Stockholm", 
        "from Stockholm to Santorini", 
        "Naples and Warsaw", 
        "Lisbon and Warsaw", 
        "Naples and Milan", 
        "Lisbon and Naples", 
        "from Riga to Tallinn", 
        "Tallinn and Prague", 
        "Stockholm and Warsaw", 
        "Riga and Warsaw", 
        "Lisbon and Riga", 
        "Riga and Stockholm", 
        "Lisbon and Porto", 
        "Lisbon and Prague", 
        "Milan and Porto", 
        "Prague and Milan", 
        "Lisbon and Milan", 
        "Warsaw and Porto", 
        "Warsaw and Tallinn", 
        "Santorini and Milan", 
        "Stockholm and Prague", 
        "Stockholm and Tallinn", 
        "Warsaw and Milan", 
        "Santorini and Naples", 
        "Warsaw and Prague"
    ]
    
    edges_set = set()
    for conn in flight_connections:
        if conn.startswith("from"):
            parts = conn.split()
            city1 = parts[1]
            city2 = parts[3]
            key = tuple(sorted([city1, city2]))
            edges_set.add(key)
        else:
            if " and " in conn:
                parts = conn.split(" and ")
                city1 = parts[0].strip()
                city2 = parts[1].strip()
                key = tuple(sorted([city1, city2]))
                edges_set.add(key)
            else:
                print(f"Unhandled connection string: {conn}")
    
    graph_edges = []
    for (a, b) in edges_set:
        i = city_index[a]
        j = city_index[b]
        graph_edges.append((i, j))
    
    s = Solver()
    n = 10
    pos = [Int(f'pos_{i}') for i in range(n)]
    
    for i in range(n):
        s.add(pos[i] >= 0, pos[i] < n)
    s.add(Distinct(pos))
    
    idx_riga = city_index['Riga']
    idx_tallinn = city_index['Tallinn']
    idx_milan = city_index['Milan']
    
    start_riga = 1
    for j in range(n):
        start_riga += If(pos[j] < pos[idx_riga], lengths[j] - 1, 0)
    s.add(start_riga >= 2, start_riga <= 8)
    
    start_tallinn = 1
    for j in range(n):
        start_tallinn += If(pos[j] < pos[idx_tallinn], lengths[j] - 1, 0)
    s.add(start_tallinn >= 16, start_tallinn <= 20)
    
    start_milan = 1
    for j in range(n):
        start_milan += If(pos[j] < pos[idx_milan], lengths[j] - 1, 0)
    s.add(start_milan >= 22, start_milan <= 26)
    
    for k in range(9):
        or_terms = []
        for (i, j) in graph_edges:
            term1 = And(pos[i] == k, pos[j] == k + 1)
            term2 = And(pos[j] == k, pos[i] == k + 1)
            or_terms.append(term1)
            or_terms.append(term2)
        s.add(Or(or_terms))
    
    if s.check() == sat:
        m = s.model()
        pos_val = [m.evaluate(pos[i]).as_long() for i in range(n)]
        
        perm_order = [0] * n
        for idx in range(n):
            p = pos_val[idx]
            perm_order[p] = idx
        
        starts = [0] * n
        starts[0] = 1
        for i in range(1, n):
            starts[i] = starts[i-1] + lengths[perm_order[i-1]] - 1
        
        itinerary = []
        for i in range(n):
            city_idx = perm_order[i]
            s_day = starts[i]
            e_day = s_day + lengths[city_idx] - 1
            itinerary.append({"day_range": f"Day {s_day}-{e_day}", "place": cities[city_idx]})
            if i < n - 1:
                itinerary.append({"day_range": f"Day {e_day}", "place": cities[city_idx]})
                next_city_idx = perm_order[i+1]
                itinerary.append({"day_range": f"Day {e_day}", "place": cities[next_city_idx]})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()