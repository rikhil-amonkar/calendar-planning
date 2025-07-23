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
    
    start = [Int(f'start_{i}') for i in range(cities)]
    end = [Int(f'end_{i}') for i in range(cities)]
    city_order = [Int(f'city_order_{i}') for i in range(cities)]
    
    for i in range(cities):
        s.add(start[i] >= 1, start[i] <= 19)
        s.add(end[i] >= 1, end[i] <= 19)
        s.add(start[i] <= end[i])
        s.add(end[i] == start[i] + req_days[i] - 1)
    
    s.add(Distinct(city_order))
    for i in range(cities):
        s.add(city_order[i] >= 0, city_order[i] < cities)
    
    first_city_constraint = Or([And(city_order[0] == i, start[i] == 1) for i in range(cities)])
    s.add(first_city_constraint)
    
    last_city_constraint = Or([And(city_order[cities-1] == i, end[i] == 19) for i in range(cities)])
    s.add(last_city_constraint)
    
    for pos in range(cities - 1):
        cons = Or([And(city_order[pos] == i, city_order[pos+1] == j, end[i] == start[j]) 
                  for i in range(cities) for j in range(cities) if i != j])
        s.add(cons)
    
    for pos in range(cities - 1):
        edge_cons = Or([And(city_order[pos] == a, city_order[pos+1] == b) for (a, b) in edges])
        s.add(edge_cons)
    
    istanbul_index = city_names.index("Istanbul")
    oslo_index = city_names.index("Oslo")
    s.add(start[istanbul_index] <= 8, end[istanbul_index] >= 5)
    s.add(start[oslo_index] <= 9, end[oslo_index] >= 8)
    
    if s.check() == sat:
        m = s.model()
        seq_val = [m.evaluate(city_order[i]).as_long() for i in range(cities)]
        start_val = [m.evaluate(start[i]).as_long() for i in range(cities)]
        end_val = [m.evaluate(end[i]).as_long() for i in range(cities)]
        
        itinerary = []
        for pos in range(cities):
            city_idx = seq_val[pos]
            s_day = start_val[city_idx]
            e_day = end_val[city_idx]
            itinerary.append({
                'day_range': f"Day {s_day}-{e_day}",
                'place': city_names[city_idx]
            })
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()