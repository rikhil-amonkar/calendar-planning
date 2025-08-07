from z3 import *
import json

def main():
    cities = ["Bucharest", "Tallinn", "Seville", "Stockholm", "Munich", "Milan"]
    durations = [4, 2, 5, 5, 5, 2]
    n = len(cities)
    
    idx = {city: i for i, city in enumerate(cities)}
    flight_pairs = [
        ("Milan", "Stockholm"),
        ("Munich", "Stockholm"),
        ("Bucharest", "Munich"),
        ("Munich", "Seville"),
        ("Stockholm", "Tallinn"),
        ("Munich", "Milan"),
        ("Munich", "Tallinn"),
        ("Seville", "Milan")
    ]
    flight_edges = []
    for u, v in flight_pairs:
        i_u = idx[u]
        i_v = idx[v]
        flight_edges.append((min(i_u, i_v), max(i_u, i_v)))
    
    order = [Int('o%d' % i) for i in range(n)]
    s = Solver()
    
    for i in range(n):
        s.add(order[i] >= 0, order[i] < n)
    s.add(Distinct(order))
    
    for i in range(n-1):
        a = order[i]
        b = order[i+1]
        edge_conds = []
        for (u, v) in flight_edges:
            edge_conds.append(And(a == u, b == v))
            edge_conds.append(And(a == v, b == u))
        s.add(Or(edge_conds))
    
    pos_vars = [Int('pos_%d' % i) for i in range(n)]
    for c in range(n):
        s.add(pos_vars[c] == Sum([If(order[i] == c, i, 0) for i in range(n)]))
    
    start_vars = [Int('start_%d' % i) for i in range(n)]
    for c in range(n):
        sum_before = Sum([If(And(d != c, pos_vars[d] < pos_vars[c]), durations[d], 0) for d in range(n)])
        s.add(start_vars[c] == 1 + sum_before - pos_vars[c])
    
    s.add(start_vars[idx["Bucharest"]] <= 4)
    s.add(start_vars[idx["Seville"]] >= 4, start_vars[idx["Seville"]] <= 12)
    s.add(start_vars[idx["Munich"]] <= 8)
    
    if s.check() == sat:
        m = s.model()
        order_val = [m.evaluate(order[i]).as_long() for i in range(n)]
        start_val = [m.evaluate(start_vars[i]).as_long() for i in range(n)]
        end_val = [start_val[i] + durations[i] - 1 for i in range(n)]
        
        itinerary_list = []
        for day in range(1, 19):
            places = []
            for i in range(n):
                if start_val[i] <= day <= end_val[i]:
                    places.append(cities[i])
            itinerary_list.append({"day": day, "place": places})
        
        result = {"itinerary": itinerary_list}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()