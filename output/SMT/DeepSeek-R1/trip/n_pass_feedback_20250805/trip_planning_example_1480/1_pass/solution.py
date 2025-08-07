from z3 import *
import json

def main():
    cities = ["Geneva", "Venice", "Vilnius", "Brussels", "Istanbul", "Vienna", "Riga", "Madrid", "Reykjavik", "Munich"]
    duration = [4, 5, 4, 2, 4, 4, 2, 4, 2, 5]
    
    directed_edges = [
        (0, 4), (4, 0),
        (0, 3), (3, 0),
        (0, 7), (7, 0),
        (0, 9), (9, 0),
        (0, 5), (5, 0),
        (1, 3), (3, 1),
        (1, 9), (9, 1),
        (1, 7), (7, 1),
        (1, 5), (5, 1),
        (1, 4), (4, 1),
        (2, 5), (5, 2),
        (2, 4), (4, 2),
        (2, 3), (3, 2),
        (2, 9),
        (3, 6), (6, 3),
        (3, 8), (8, 3),
        (3, 5), (5, 3),
        (4, 3), (3, 4),
        (4, 6), (6, 4),
        (4, 5), (5, 4),
        (5, 9), (9, 5),
        (5, 8), (8, 5),
        (5, 6), (6, 5),
        (6, 9),
        (6, 2),
        (7, 9), (9, 7),
        (7, 1), (1, 7),
        (7, 0), (0, 7),
        (7, 3), (3, 7),
        (7, 4), (4, 7),
        (8, 7),
        (8, 9), (9, 8),
        (8, 5), (5, 8),
        (9, 0), (0, 9),
        (9, 1), (1, 9),
        (9, 5), (5, 9),
        (9, 7), (7, 9),
        (9, 8), (8, 9),
        (9, 4), (4, 9)
    ]
    
    n = 10
    seq = [Int('seq_%i' % i) for i in range(n)]
    s = Solver()
    
    for i in range(n):
        s.add(seq[i] >= 0, seq[i] < 10)
    
    s.add(seq[0] == 0)
    s.add(seq[2] == 1)
    s.add(seq[7] == 2)
    s.add(seq[9] == 3)
    
    s.add(Distinct([seq[1], seq[3], seq[4], seq[5], seq[6], seq[8]]))
    for idx in [1, 3, 4, 5, 6, 8]:
        s.add(Or([seq[idx] == c for c in [4, 5, 6, 7, 8, 9]]))
    
    start = [Int('start_%i' % i) for i in range(n)]
    s.add(start[0] == 1)
    s.add(start[2] == 7)
    s.add(start[7] == 20)
    s.add(start[9] == 26)
    
    for i in range(9):
        s.add(start[i+1] == start[i] + duration[seq[i]] - 1)
    
    for i in range(9):
        c1 = seq[i]
        c2 = seq[i+1]
        edge_constraints = []
        for edge in directed_edges:
            edge_constraints.append(And(c1 == edge[0], c2 == edge[1]))
        s.add(Or(edge_constraints))
    
    if s.check() == sat:
        m = s.model()
        seq_val = [m.evaluate(seq[i]).as_long() for i in range(n)]
        start_val = [m.evaluate(start[i]).as_long() for i in range(n)]
        
        itinerary_list = []
        for day in range(1, 28):
            cities_today = []
            for i in range(n):
                s_day = start_val[i]
                e_day = s_day + duration[seq_val[i]] - 1
                if day >= s_day and day <= e_day:
                    cities_today.append(cities[seq_val[i]])
            itinerary_list.append({"day": day, "city": cities_today})
        
        result = {'itinerary': itinerary_list}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()