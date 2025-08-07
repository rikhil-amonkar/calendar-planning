from z3 import *
import json

def main():
    cities = ['Stockholm', 'Hamburg', 'Florence', 'Istanbul', 'Oslo', 'Vilnius', 'Santorini', 'Munich', 'Frankfurt', 'Krakow']
    req_array = [3, 5, 2, 5, 5, 5, 2, 5, 4, 5]
    
    s = Solver()
    
    req_z3 = Array('req', IntSort(), IntSort())
    for i, r in enumerate(req_array):
        req_z3 = Store(req_z3, i, r)
    
    c = [Int(f'c{i}') for i in range(10)]
    prefix = [Int(f'prefix{i}') for i in range(10)]
    
    for i in range(10):
        s.add(And(c[i] >= 0, c[i] < 10))
    s.add(Distinct(c))
    
    s.add(prefix[0] == req_z3[c[0]])
    for i in range(1, 10):
        s.add(prefix[i] == prefix[i-1] + req_z3[c[i]])
    
    s.add(prefix[9] - 9 == 32)
    
    for pos in range(1, 10):
        s.add(Implies(c[pos] == 9, (prefix[pos-1] - (pos-1)) == 5))
        s.add(Implies(c[pos] == 3, (prefix[pos-1] - (pos-1)) == 25))
    
    bidirectional = [
        (0,4), (4,0),
        (9,8), (8,9),
        (9,3), (3,9),
        (7,0), (0,7),
        (1,0), (0,1),
        (4,3), (3,4),
        (3,0), (0,3),
        (4,9), (9,4),
        (5,3), (3,5),
        (4,8), (8,4),
        (8,2), (2,8),
        (8,7), (7,8),
        (4,1), (1,4),
        (5,8), (8,5),
        (9,7), (7,9),
        (1,3), (3,1),
        (8,0), (0,8),
        (7,1), (1,7)
    ]
    directed = [
        (9,5),
        (2,7),
        (0,6),
        (6,4),
        (5,7)
    ]
    edges = bidirectional + directed
    
    for i in range(9):
        edge_constraints = []
        for (u, v) in edges:
            edge_constraints.append(And(c[i] == u, c[i+1] == v))
        s.add(Or(edge_constraints))
    
    if s.check() == sat:
        m = s.model()
        c_val = [m.evaluate(c[i]).as_long() for i in range(10)]
        prefix_val = [m.evaluate(prefix[i]).as_long() for i in range(10)]
        
        starts = []
        ends = []
        for i in range(10):
            if i == 0:
                start_i = 1
            else:
                start_i = prefix_val[i-1] - (i-1)
            end_i = prefix_val[i] - i
            starts.append(start_i)
            ends.append(end_i)
        
        itinerary_list = []
        for day in range(1, 33):
            for i in range(10):
                if day >= starts[i] and day <= ends[i]:
                    itinerary_list.append({'day': day, 'place': cities[c_val[i]]})
        
        result = {'itinerary': itinerary_list}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()