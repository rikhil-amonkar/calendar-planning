import json
from z3 import *

def main():
    cities = ["Lisbon", "Dubrovnik", "Copenhagen", "Prague", "Tallinn", "Stockholm", "Split", "Lyon"]
    n = 8
    days = [2, 5, 5, 3, 2, 4, 3, 2]  # in the order of the cities list

    flight_pairs_str = [
        ("Dubrovnik", "Stockholm"),
        ("Lisbon", "Copenhagen"),
        ("Lisbon", "Lyon"),
        ("Copenhagen", "Stockholm"),
        ("Copenhagen", "Split"),
        ("Prague", "Stockholm"),
        ("Tallinn", "Stockholm"),
        ("Prague", "Lyon"),
        ("Lisbon", "Stockholm"),
        ("Prague", "Lisbon"),
        ("Stockholm", "Split"),
        ("Prague", "Copenhagen"),
        ("Split", "Lyon"),
        ("Copenhagen", "Dubrovnik"),
        ("Prague", "Split"),
        ("Tallinn", "Copenhagen"),
        ("Tallinn", "Prague")
    ]
    
    flight_pairs = []
    for a, b in flight_pairs_str:
        idx_a = cities.index(a)
        idx_b = cities.index(b)
        flight_pairs.append((idx_a, idx_b))
        flight_pairs.append((idx_b, idx_a))
    
    solver = Solver()
    
    order = [Int('o%d' % i) for i in range(n)]
    solver.add([And(order[i] >= 0, order[i] < n) for i in range(n)])
    solver.add(Distinct(order))
    solver.add(order[7] == 7)  # Lyon is last

    pos = [Int('p%d' % i) for i in range(n)]
    solver.add([And(pos[i] >= 0, pos[i] < n) for i in range(n)])
    
    for i in range(n):
        or_list = []
        for j in range(n):
            or_list.append(And(order[j] == i, pos[i] == j))
        solver.add(Or(or_list))
    
    start = [Int('start%d' % i) for i in range(n)]
    for i in range(n):
        expr = 1
        for j in range(n):
            if j == i:
                continue
            expr = expr + If(And(j != i, pos[j] < pos[i]), days[j] - 1, 0)
        solver.add(start[i] == expr)
    
    solver.add(start[7] == 18)  # Lyon starts at day 18
    solver.add(start[0] >= 3, start[0] <= 5)  # Lisbon
    solver.add(start[4] >= 1, start[4] <= 2)   # Tallinn
    solver.add(start[5] >= 10, start[5] <= 16) # Stockholm

    for k in range(7):
        or_constraints = []
        for (a, b) in flight_pairs:
            or_constraints.append(And(order[k] == a, order[k+1] == b))
        solver.add(Or(or_constraints))
    
    if solver.check() == sat:
        m = solver.model()
        order_list = [m[order[i]].as_long() for i in range(n)]
        start_list = [m.evaluate(start[i]).as_long() for i in range(n)]
        
        itinerary = []
        for idx in range(n):
            city_idx = order_list[idx]
            city_name = cities[city_idx]
            s = start_list[city_idx]
            d = days[city_idx]
            e = s + d - 1
            itinerary.append({"day_range": "Day {}-{}".format(s, e), "place": city_name})
            if idx < n-1:
                next_city_idx = order_list[idx+1]
                next_city_name = cities[next_city_idx]
                itinerary.append({"day_range": "Day {}".format(e), "place": city_name})
                itinerary.append({"day_range": "Day {}".format(e), "place": next_city_name})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()