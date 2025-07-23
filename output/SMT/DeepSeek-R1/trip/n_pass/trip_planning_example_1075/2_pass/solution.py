from z3 import *
import json

def main():
    cities = ["Vienna", "Lyon", "Edinburgh", "Reykjavik", "Stuttgart", "Manchester", "Split", "Prague"]
    durations = [4, 3, 4, 5, 5, 2, 5, 4]
    edges = [
        (0, 1), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7),
        (1, 6), (1, 7),
        (2, 4), (2, 7),
        (3, 4), (3, 7),
        (4, 5), (4, 6),
        (5, 6), (5, 7),
        (6, 7)
    ]
    
    s = Solver()
    order = [Int('o%d' % i) for i in range(8)]
    pos_start = [Int('ps%d' % i) for i in range(8)]
    
    dur_array = Array('durations', IntSort(), IntSort())
    for i in range(8):
        dur_array = Store(dur_array, i, durations[i])
    
    for k in range(8):
        s.add(order[k] >= 0, order[k] < 8)
    s.add(Distinct(order))
    
    s.add(pos_start[0] == 1)
    for k in range(7):
        s.add(pos_start[k+1] == pos_start[k] + dur_array[order[k]] - 1)
    s.add(pos_start[7] + dur_array[order[7]] - 1 == 25)
    
    edinburgh_index = 2
    s.add(Or([And(order[k] == edinburgh_index, pos_start[k] == 5) for k in range(8)]))
    
    split_index = 6
    s.add(Or([And(order[k] == split_index, pos_start[k] >= 15, pos_start[k] <= 21) for k in range(8)]))
    
    for k in range(7):
        edge_conds = []
        for (a, b) in edges:
            edge_conds.append(And(order[k] == a, order[k+1] == b))
            edge_conds.append(And(order[k] == b, order[k+1] == a))
        s.add(Or(edge_conds))
    
    if s.check() == sat:
        m = s.model()
        city_starts = [0] * 8
        for k in range(8):
            city_index = m.evaluate(order[k]).as_long()
            start_day = m.evaluate(pos_start[k]).as_long()
            city_starts[city_index] = start_day
        
        itinerary = []
        for day in range(1, 26):
            cities_today = []
            for i in range(8):
                start = city_starts[i]
                end = start + durations[i] - 1
                if start <= day <= end:
                    cities_today.append(cities[i])
            for city in sorted(cities_today):
                itinerary.append({"day": day, "place": city})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()