from z3 import *
import json

def main():
    cities = ["Vienna", "Milan", "Rome", "Riga", "Lisbon", "Vilnius", "Oslo"]
    n_days = 15
    edges = [
        (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6),
        (1, 3), (1, 5), (1, 6),
        (2, 3), (2, 4), (2, 6),
        (3, 4), (3, 5), (3, 6),
        (4, 6),
        (5, 6)
    ]
    
    s = Solver()
    x = [Int('x_%d' % i) for i in range(n_days)]
    
    for i in range(n_days):
        s.add(x[i] >= 0)
        s.add(x[i] < len(cities))
    
    s.add(x[0] == 0)
    s.add(Or(x[2] == 0, x[3] == 0))
    
    allowed_pairs = []
    for (a, b) in edges:
        allowed_pairs.append((a, b))
        allowed_pairs.append((b, a))
    
    for i in range(n_days - 1):
        cond = (x[i] != x[i+1])
        flight_constraint = Or([And(x[i] == a, x[i+1] == b) for (a, b) in allowed_pairs])
        s.add(Implies(cond, flight_constraint))
    
    total_days = [0] * len(cities)
    for c in range(len(cities)):
        in_set = [If(x[0] == c, 1, 0)]
        for i in range(1, n_days):
            in_set.append(If(Or(x[i-1] == c, x[i] == c), 1, 0))
        total_days[c] = sum(in_set)
    
    req_days = [4, 2, 3, 2, 3, 4, 3]
    for c in range(len(cities)):
        s.add(total_days[c] == req_days[c])
    
    s.add(Or(x[9] == 4, x[10] == 4, x[11] == 4, x[12] == 4))
    s.add(Or(x[12] == 6, x[13] == 6, x[14] == 6))
    
    flight_count = Sum([If(x[i] != x[i+1], 1, 0) for i in range(n_days-1)])
    s.add(flight_count == 6)
    
    if s.check() == sat:
        m = s.model()
        x_val = [m.evaluate(x[i]).as_long() for i in range(n_days)]
        itinerary = []
        start = 0
        current_city = x_val[0]
        for i in range(1, n_days):
            if x_val[i] != current_city:
                day_range = f"Day {start+1}-{i}"
                itinerary.append({"day_range": day_range, "place": cities[current_city]})
                start = i
                current_city = x_val[i]
        day_range = f"Day {start+1}-{n_days}"
        itinerary.append({"day_range": day_range, "place": cities[current_city]})
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()