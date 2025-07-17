from z3 import *
import json

def main():
    cities = ['Stockholm', 'Hamburg', 'Florence', 'Istanbul', 'Oslo', 'Vilnius', 'Santorini', 'Munich', 'Frankfurt', 'Krakow']
    city_dict = {i: name for i, name in enumerate(cities)}
    durations_arr = [3, 5, 2, 5, 5, 5, 2, 5, 4, 5]
    
    allowed_edges = [
        (0,4), (4,0), (9,8), (8,9), (9,3), (3,9), (7,0), (0,7), (1,0), (0,1),
        (4,3), (3,4), (3,0), (0,3), (4,9), (9,4), (5,3), (3,5), (4,5), (5,4),
        (8,3), (3,8), (4,8), (8,4), (7,1), (1,7), (7,3), (3,7), (4,7), (7,4),
        (8,2),  # Only Frankfurt to Florence allowed, not the reverse
        (4,1), (1,4), (5,8), (8,5), (9,7), (7,9), (1,3), (3,1),
        (8,0), (0,8), (8,7), (7,8), (9,0), (0,9), (9,5), (2,7), (0,6), (6,4), (5,7)
    ]
    
    s = Solver()
    
    c = [Int('c_%d' % i) for i in range(10)]
    for i in range(10):
        s.add(c[i] >= 0, c[i] <= 9)
    s.add(Distinct(c))
    
    durations_arr_z3 = Array('durations', IntSort(), IntSort())
    for j in range(10):
        s.add(durations_arr_z3[j] == durations_arr[j])
    
    dur_seq = [Select(durations_arr_z3, c[i]) for i in range(10)]
    
    S = [dur_seq[0] - 1]
    for i in range(1, 10):
        S.append(S[i-1] + (dur_seq[i] - 1))
    s.add(S[9] == 31)
    
    k = Int('k')
    s.add(k >= 0, k < 10)
    l_var = Int('l')
    s.add(l_var >= 0, l_var < 10)
    
    s.add(Or([And(c[i] == 9, k == i) for i in range(10)]))
    s.add(Or([And(c[i] == 3, l_var == i) for i in range(10)]))
    s.add(k < l_var)
    s.add(k > 0, l_var > 0)
    
    s.add(Or([And(k == i, S[i-1] == 4) for i in range(1,10)]))
    s.add(Or([And(l_var == i, S[i-1] == 24) for i in range(1,10)]))
    
    for i in range(9):
        constraints = []
        for edge in allowed_edges:
            u, v = edge
            constraints.append(And(c[i] == u, c[i+1] == v))
        s.add(Or(constraints))
    
    if s.check() == sat:
        model = s.model()
        seq = [model.evaluate(c[i]).as_long() for i in range(10)]
        k_val = model.evaluate(k).as_long()
        l_val = model.evaluate(l_var).as_long()
        
        a = [0] * 10
        d = [0] * 10
        a[0] = 1
        d[0] = a[0] + durations_arr[seq[0]] - 1
        for i in range(1, 10):
            a[i] = d[i-1]
            d[i] = a[i] + durations_arr[seq[i]] - 1
        
        itinerary = []
        for i in range(10):
            city_name = city_dict[seq[i]]
            if a[i] == d[i]:
                day_range_str = "Day %d" % a[i]
            else:
                day_range_str = "Day %d-%d" % (a[i], d[i])
            itinerary.append({"day_range": day_range_str, "place": city_name})
            
            if i < 9:
                day = d[i]
                itinerary.append({"day_range": "Day %d" % day, "place": city_name})
                next_city_name = city_dict[seq[i+1]]
                itinerary.append({"day_range": "Day %d" % day, "place": next_city_name})
        
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()