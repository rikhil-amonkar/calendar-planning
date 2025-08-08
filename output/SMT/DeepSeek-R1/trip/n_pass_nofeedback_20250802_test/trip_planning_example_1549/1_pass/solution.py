from z3 import *
import json

def main():
    cities = ["Prague", "Tallinn", "Warsaw", "Porto", "Naples", "Milan", "Lisbon", "Santorini", "Riga", "Stockholm"]
    reqs = [5, 3, 2, 3, 5, 3, 5, 5, 4, 2]
    
    bidirectional_pairs = [
        ("Riga", "Prague"),
        ("Stockholm", "Milan"),
        ("Riga", "Milan"),
        ("Lisbon", "Stockholm"),
        ("Naples", "Warsaw"),
        ("Lisbon", "Warsaw"),
        ("Naples", "Milan"),
        ("Lisbon", "Naples"),
        ("Tallinn", "Prague"),
        ("Stockholm", "Warsaw"),
        ("Riga", "Warsaw"),
        ("Lisbon", "Riga"),
        ("Riga", "Stockholm"),
        ("Lisbon", "Porto"),
        ("Lisbon", "Prague"),
        ("Milan", "Porto"),
        ("Prague", "Milan"),
        ("Lisbon", "Milan"),
        ("Warsaw", "Porto"),
        ("Warsaw", "Tallinn"),
        ("Santorini", "Milan"),
        ("Stockholm", "Prague"),
        ("Stockholm", "Tallinn"),
        ("Warsaw", "Milan"),
        ("Santorini", "Naples"),
        ("Warsaw", "Prague")
    ]
    
    unidirectional = [
        ("Stockholm", "Santorini"),
        ("Riga", "Tallinn")
    ]
    
    edges = set()
    for A, B in bidirectional_pairs:
        idxA = cities.index(A)
        idxB = cities.index(B)
        edges.add((idxA, idxB))
        edges.add((idxB, idxA))
    for A, B in unidirectional:
        idxA = cities.index(A)
        idxB = cities.index(B)
        edges.add((idxA, idxB))
    
    s = Solver()
    
    order = [Int(f'order_{i}') for i in range(10)]
    for i in range(10):
        s.add(order[i] >= 0, order[i] < 10)
    s.add(Distinct(order))
    
    S = [Int(f'S_{i}') for i in range(10)]
    s.add(S[0] == reqs[order[0]])
    for i in range(1, 10):
        s.add(S[i] == S[i-1] + reqs[order[i]])
    
    riga_index = cities.index("Riga")
    riga_constraint = Or([And(order[pos] == riga_index, S[pos-1] == pos + 5) for pos in range(1, 10)])
    s.add(riga_constraint)
    
    tallinn_index = cities.index("Tallinn")
    tallinn_constraint = True
    for k in range(1, 9):
        d_in = S[k-1] - (k-1)
        tallinn_constraint = And(tallinn_constraint, Implies(order[k] == tallinn_index, And(d_in >= 16, d_in <= 20)))
    s.add(tallinn_constraint)
    
    milan_index = cities.index("Milan")
    case1 = And(order[9] == milan_index, S[8] == 34)
    case2 = True
    for k in range(1, 9):
        d_in = S[k-1] - (k-1)
        case2 = And(case2, Implies(order[k] == milan_index, And(d_in >= 22, d_in <= 26)))
    s.add(Or(case1, case2))
    
    for i in range(9):
        valid_edge = Or([And(order[i] == a, order[i+1] == b) for (a, b) in edges])
        s.add(valid_edge)
    
    if s.check() == sat:
        m = s.model()
        order_val = [m.evaluate(order[i]).as_long() for i in range(10)]
        S_val = [0] * 10
        S_val[0] = reqs[order_val[0]]
        for i in range(1, 10):
            S_val[i] = S_val[i-1] + reqs[order_val[i]]
        d = [S_val[i] - i for i in range(9)]
        
        itinerary = []
        start_day = 1
        for i in range(9):
            end_day = d[i]
            city_name = cities[order_val[i]]
            for day in range(start_day, end_day + 1):
                itinerary.append({"day": day, "place": city_name})
            start_day = end_day + 1
        
        last_city = cities[order_val[9]]
        for day in range(d[8], 29):
            itinerary.append({"day": day, "place": last_city})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()