from z3 import *

def main():
    d = [Int('d_%d' % i) for i in range(11)]
    C = [Int('C_%d' % i) for i in range(10)]
    
    s = Solver()
    
    city_names = {
        0: "Venice",
        1: "Reykjavik",
        2: "Munich",
        3: "Santorini",
        4: "Manchester",
        5: "Porto",
        6: "Bucharest",
        7: "Tallinn",
        8: "Valencia",
        9: "Vienna"
    }
    
    allowed_edges = [
        (6,4), (4,6), 
        (2,0), (0,2),
        (3,4), (4,3),
        (9,1), (1,9),
        (0,3), (3,0),
        (2,5), (5,2),
        (8,9), (9,8),
        (4,9), (9,4),
        (5,9), (9,5),
        (0,4), (4,0),
        (3,9), (9,3),
        (2,4), (4,2),
        (2,1), (1,2),
        (6,8), (8,6),
        (0,9), (9,0),
        (6,9), (9,6),
        (5,4), (4,5),
        (2,9), (9,2),
        (8,5), (5,8),
        (2,6), (6,2),
        (7,2), (2,7),
        (3,6), (6,3),
        (2,8), (8,2)
    ]
    
    s.add(d[0] == 1)
    s.add(d[10] == 24)
    
    for i in range(10):
        s.add(d[i] >= 1, d[i] <= 24)
        s.add(d[i] < d[i+1])
    
    s.add(Distinct(C))
    for i in range(10):
        s.add(C[i] >= 0, C[i] <= 9)
    
    for i in range(10):
        s.add(Implies(C[i] == 2, And(d[i] == 4, d[i+1] == 6)))
        s.add(Implies(C[i] == 3, And(d[i] == 8, d[i+1] == 10)))
        s.add(Implies(C[i] == 8, And(d[i] == 14, d[i+1] == 15)))
        
        s.add(Implies(C[i] == 0, d[i+1] == d[i] + 2))
        s.add(Implies(C[i] == 1, d[i+1] == d[i] + 1))
        s.add(Implies(C[i] == 2, d[i+1] == d[i] + 2))
        s.add(Implies(C[i] == 3, d[i+1] == d[i] + 2))
        s.add(Implies(C[i] == 4, d[i+1] == d[i] + 2))
        s.add(Implies(C[i] == 5, d[i+1] == d[i] + 2))
        s.add(Implies(C[i] == 6, d[i+1] == d[i] + 4))
        s.add(Implies(C[i] == 7, d[i+1] == d[i] + 3))
        s.add(Implies(C[i] == 8, d[i+1] == d[i] + 1))
        s.add(Implies(C[i] == 9, d[i+1] == d[i] + 4))
    
    for i in range(9):
        constraints = []
        for edge in allowed_edges:
            a, b = edge
            constraints.append(And(C[i] == a, C[i+1] == b))
        s.add(Or(constraints))
    
    if s.check() == sat:
        m = s.model()
        d_vals = [m.evaluate(d_i).as_long() for d_i in d]
        C_vals = [m.evaluate(C_i).as_long() for C_i in C]
        
        itinerary = []
        
        # First block (block0)
        a0 = d_vals[0]
        a1 = d_vals[1]
        city0_name = city_names[C_vals[0]]
        itinerary.append({"day_range": "Day %d-%d" % (a0, a1), "place": city0_name})
        itinerary.append({"day_range": "Day %d" % (a1), "place": city0_name})
        
        # Blocks 1 to 8
        for i in range(1, 9):
            a_i = d_vals[i]
            a_i_plus_1 = d_vals[i+1]
            city_i_name = city_names[C_vals[i]]
            itinerary.append({"day_range": "Day %d" % (a_i), "place": city_i_name})
            itinerary.append({"day_range": "Day %d-%d" % (a_i, a_i_plus_1), "place": city_i_name})
            itinerary.append({"day_range": "Day %d" % (a_i_plus_1), "place": city_i_name})
        
        # Last block (block9)
        a9 = d_vals[9]
        a10 = d_vals[10]
        city9_name = city_names[C_vals[9]]
        itinerary.append({"day_range": "Day %d" % (a9), "place": city9_name})
        itinerary.append({"day_range": "Day %d-%d" % (a9, a10), "place": city9_name})
        
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == '__main__':
    main()