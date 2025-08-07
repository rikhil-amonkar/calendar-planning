from z3 import *
import json

def main():
    city_names = ["Bucharest", "Tallinn", "Seville", "Stockholm", "Munich", "Milan"]
    d = [4, 2, 5, 5, 5, 2]  # durations

    flight_edges = [
        ("Milan", "Stockholm"), ("Munich", "Stockholm"),
        ("Bucharest", "Munich"), ("Munich", "Seville"),
        ("Stockholm", "Tallinn"), ("Munich", "Milan"),
        ("Munich", "Tallinn"), ("Seville", "Milan")
    ]
    flight_edges_set = set()
    for a, b in flight_edges:
        i = city_names.index(a)
        j = city_names.index(b)
        flight_edges_set.add((i, j))

    n = 6
    s = Solver()

    # City order variables
    order = [Int('o%d' % i) for i in range(n)]
    for i in range(n):
        s.add(And(order[i] >= 0, order[i] < n))
    s.add(Distinct(order))

    # Start position variables
    start_pos = [Int('sp%d' % i) for i in range(n)]
    s.add(start_pos[0] == 1)
    
    # Duration lookup helper
    def duration(city_idx):
        return If(city_idx == 0, d[0],
               If(city_idx == 1, d[1],
               If(city_idx == 2, d[2],
               If(city_idx == 3, d[3],
               If(city_idx == 4, d[4], d[5])))))
    
    # Chain start positions
    for i in range(1, n):
        prev_duration = duration(order[i-1])
        s.add(start_pos[i] == start_pos[i-1] + prev_duration - 1)
    
    # City start days
    city_start = [Int('cs%d' % i) for i in range(n)]
    for c in range(n):
        s.add(city_start[c] == 
              If(order[0] == c, start_pos[0],
              If(order[1] == c, start_pos[1],
              If(order[2] == c, start_pos[2],
              If(order[3] == c, start_pos[3],
              If(order[4] == c, start_pos[4], start_pos[5])))))
    
    # Event constraints
    s.add(city_start[0] <= 4)   # Bucharest by day 4
    s.add(city_start[4] <= 8)   # Munich by day 8
    s.add(And(city_start[2] >= 4, city_start[2] <= 12))  # Seville between 4-12
    
    # Flight constraints
    for i in range(n-1):
        c1 = order[i]
        c2 = order[i+1]
        edge_constraints = []
        for (a, b) in flight_edges_set:
            edge_constraints.append(Or(And(c1 == a, c2 == b), And(c1 == b, c2 == a)))
        s.add(Or(edge_constraints))

    if s.check() == sat:
        m = s.model()
        order_val = [m.evaluate(order[i]).as_long() for i in range(n)]
        start_val = [m.evaluate(start_pos[i]).as_long() for i in range(n)]
        
        itinerary = []
        for c in order_val:
            start = start_val[order_val.index(c)]
            end = start + d[c] - 1
            itinerary.append({
                "day_range": f"Day {start}-{end}",
                "place": city_names[c]
            })
        
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()