from z3 import *
import json

def main():
    s = Solver()
    
    cities = 6
    req_days = [5, 4, 5, 2, 3, 5]
    city_names = ["Reykjavik", "Istanbul", "Edinburgh", "Oslo", "Stuttgart", "Bucharest"]
    
    edges = [
        (5, 3), (3, 5),  # Bucharest <-> Oslo
        (5, 1), (1, 5),  # Bucharest <-> Istanbul
        (1, 3), (3, 1),  # Istanbul <-> Oslo
        (1, 2), (2, 1),  # Istanbul <-> Edinburgh
        (1, 4), (4, 1),  # Istanbul <-> Stuttgart
        (0, 4),          # Reykjavik -> Stuttgart
        (3, 0), (0, 3),  # Oslo <-> Reykjavik
        (3, 2), (2, 3),  # Oslo <-> Edinburgh
        (4, 2), (2, 4)   # Stuttgart <-> Edinburgh
    ]
    
    seq = [Int(f'seq_{i}') for i in range(cities)]
    start = [Int(f'start_{i}') for i in range(cities)]
    end = [Int(f'end_{i}') for i in range(cities)]
    
    s.add(Distinct(seq))
    for i in range(cities):
        s.add(seq[i] >= 0, seq[i] < cities)
    
    s.add(start[seq[0]] == 1)
    s.add(end[seq[0]] == 1 + req_days[seq[0]] - 1)
    
    for k in range(1, cities):
        s.add(start[seq[k]] == end[seq[k-1]])
        s.add(end[seq[k]] == start[seq[k]] + req_days[seq[k]] - 1)
    
    s.add(end[seq[cities-1]] == 19)
    
    for k in range(cities-1):
        edge_exists = Or([And(seq[k] == a, seq[k+1] == b) for (a, b) in edges])
        s.add(edge_exists)
    
    istanbul_index = city_names.index("Istanbul")
    oslo_index = city_names.index("Oslo")
    s.add(start[istanbul_index] <= 8, end[istanbul_index] >= 5)
    s.add(start[oslo_index] <= 9, end[oslo_index] >= 8)
    
    if s.check() == sat:
        m = s.model()
        seq_val = [m.evaluate(seq[i]).as_long() for i in range(cities)]
        start_val = [m.evaluate(start[i]).as_long() for i in range(cities)]
        end_val = [m.evaluate(end[i]).as_long() for i in range(cities)]
        
        itinerary = []
        for city_index in range(cities):
            s_day = start_val[city_index]
            e_day = end_val[city_index]
            for day in range(s_day, e_day + 1):
                itinerary.append({"day": day, "place": city_names[city_index]})
        
        itinerary_sorted = sorted(itinerary, key=lambda x: x['day'])
        result = {"itinerary": itinerary_sorted}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()