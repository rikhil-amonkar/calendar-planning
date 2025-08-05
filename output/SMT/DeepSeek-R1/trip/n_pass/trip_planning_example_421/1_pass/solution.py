from z3 import *
import json

def main():
    CityNames = ["Nice", "Dublin", "Krakow", "Lyon", "Frankfurt"]
    req_by_index = [5, 7, 6, 4, 2]
    
    adj = [
        [0, 1, 0, 1, 1],
        [1, 0, 1, 1, 1],
        [0, 1, 0, 0, 1],
        [1, 1, 0, 0, 1],
        [1, 1, 1, 1, 0]
    ]
    
    allowed_pairs = []
    for i in range(5):
        for j in range(5):
            if adj[i][j] == 1:
                allowed_pairs.append((i, j))
    
    segment_city = [Int(f'c{i}') for i in range(5)]
    solver = Solver()
    
    for i in range(5):
        solver.add(segment_city[i] >= 0, segment_city[i] <= 4)
    solver.add(Distinct(segment_city))
    
    s = [1]
    L_expr = []
    for i in range(5):
        L_i = If(segment_city[i] == 0, req_by_index[0],
                If(segment_city[i] == 1, req_by_index[1],
                If(segment_city[i] == 2, req_by_index[2],
                If(segment_city[i] == 3, req_by_index[3],
                req_by_index[4]))))
        L_expr.append(L_i)
    
    for i in range(1, 5):
        s_i = s[i-1] + L_expr[i-1] - 1
        s.append(s_i)
    
    nice_constraint = True
    for i in range(5):
        nice_constraint = And(nice_constraint, 
                             If(segment_city[i] == 0, s[i] <= 5, True))
    solver.add(nice_constraint)
    
    frankfurt_constraint = True
    for i in range(5):
        frankfurt_constraint = And(frankfurt_constraint,
                                  If(segment_city[i] == 4, Or(s[i] == 18, s[i] == 19), True))
    solver.add(frankfurt_constraint)
    
    for idx in range(4):
        c1 = segment_city[idx]
        c2 = segment_city[idx+1]
        or_constraint = Or([And(c1 == p0, c2 == p1) for (p0, p1) in allowed_pairs])
        solver.add(or_constraint)
    
    if solver.check() == sat:
        m = solver.model()
        s_val = [m.eval(s_i).as_long() for s_i in s]
        L_val = [m.eval(L_i).as_long() for L_i in L_expr]
        city_val = [m.eval(c).as_long() for c in segment_city]
        city_names = [CityNames[i] for i in city_val]
        
        itinerary = []
        for day in range(1, 21):
            for seg in range(5):
                start = s_val[seg]
                end = start + L_val[seg] - 1
                if day >= start and day <= end:
                    itinerary.append({"day": day, "place": city_names[seg]})
        
        result = {'itinerary': itinerary}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()