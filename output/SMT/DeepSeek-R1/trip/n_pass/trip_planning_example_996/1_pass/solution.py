from z3 import *
import json

def main():
    cities = ["Mykonos", "Nice", "Zurich", "Prague", "Bucharest", "Riga", "Valencia"]
    days = [3, 2, 5, 3, 5, 5, 5]
    dminus = [d - 1 for d in days]
    
    adj = [
        [0, 1, 1, 0, 0, 0, 0],
        [1, 0, 1, 0, 0, 1, 0],
        [1, 1, 0, 1, 1, 1, 1],
        [0, 0, 1, 0, 1, 1, 1],
        [0, 0, 1, 1, 0, 1, 1],
        [0, 1, 1, 1, 1, 0, 0],
        [0, 0, 1, 1, 1, 0, 0]
    ]
    
    directed_edges = []
    for a in range(7):
        for b in range(7):
            if adj[a][b] == 1:
                directed_edges.append((a, b))
    
    solver = Solver()
    city_vars = [Int('city%d' % i) for i in range(7)]
    
    for i in range(7):
        solver.add(city_vars[i] >= 0, city_vars[i] <= 6)
    solver.add(Distinct(city_vars))
    
    dminus_arr = Array('dminus_arr', IntSort(), IntSort())
    for i in range(7):
        solver.add(dminus_arr[i] == dminus[i])
    
    s = [None] * 7
    s[0] = 1
    for i in range(1, 7):
        s[i] = s[i-1] + dminus_arr[city_vars[i-1]]
    
    for i in range(7):
        solver.add(If(city_vars[i] == 0, s[i] <= 3, True))
        solver.add(If(city_vars[i] == 3, And(s[i] >= 5, s[i] <= 9), True))
    
    for i in range(6):
        edge_conds = []
        for (a, b) in directed_edges:
            edge_conds.append(And(city_vars[i] == a, city_vars[i+1] == b))
        solver.add(Or(edge_conds))
    
    if solver.check() == sat:
        model = solver.model()
        order = [model.evaluate(city_vars[i]).as_long() for i in range(7)]
        s_val = [1]
        for i in range(1, 7):
            s_val.append(model.evaluate(s[i]).as_long())
        
        itinerary = []
        for i in range(7):
            c_index = order[i]
            start = s_val[i]
            end = start + days[c_index] - 1
            itinerary.append({"day_range": "Day {}-{}".format(start, end), "place": cities[c_index]})
            if i < 6:
                itinerary.append({"day_range": "Day {}".format(end), "place": cities[c_index]})
                next_index = order[i+1]
                itinerary.append({"day_range": "Day {}".format(end), "place": cities[next_index]})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"error": "No solution found"}))

if __name__ == '__main__':
    main()