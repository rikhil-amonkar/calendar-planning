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
    start_days = [Int(f's{i}') for i in range(5)]
    solver = Solver()
    
    for i in range(5):
        solver.add(segment_city[i] >= 0, segment_city[i] <= 4)
    solver.add(Distinct(segment_city))
    
    L_expr = []
    for i in range(5):
        L_i = If(segment_city[i] == 0, req_by_index[0],
                If(segment_city[i] == 1, req_by_index[1],
                If(segment_city[i] == 2, req_by_index[2],
                If(segment_city[i] == 3, req_by_index[3],
                req_by_index[4]))))
        L_expr.append(L_i)
    
    solver.add(start_days[0] == 1)
    for i in range(1, 5):
        solver.add(start_days[i] == start_days[i-1] + L_expr[i-1])
    solver.add(start_days[4] + L_expr[4] - 1 == 20)
    
    for i in range(5):
        solver.add(If(segment_city[i] == 0, start_days[i] == 1, True))
        solver.add(If(segment_city[i] == 4, And(start_days[i] >= 18, start_days[i] <= 19), True))
    
    for idx in range(4):
        c1 = segment_city[idx]
        c2 = segment_city[idx+1]
        or_constraint = Or([And(c1 == p0, c2 == p1) for (p0, p1) in allowed_pairs])
        solver.add(or_constraint)
    
    if solver.check() == sat:
        m = solver.model()
        s_val = [m.eval(start_days[i]).as_long() for i in range(5)]
        city_val = [m.eval(segment_city[i]).as_long() for i in range(5)]
        itinerary = []
        for seg in range(5):
            start = s_val[seg]
            city_index = city_val[seg]
            length = req_by_index[city_index]
            end = start + length - 1
            for day in range(start, end + 1):
                itinerary.append({"day": day, "place": CityNames[city_index]})
        result = {'itinerary': itinerary}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()