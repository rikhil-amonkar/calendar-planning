from z3 import Solver, Int, Distinct, If, Or, And, sat, Sum
import json

def main():
    cities = {0: "Reykjavik", 1: "Riga", 2: "Warsaw", 3: "Istanbul", 4: "Krakow"}
    dur_map = [7, 2, 3, 6, 7]  # durations for cities in order: Reykjavik, Riga, Warsaw, Istanbul, Krakow
    
    edges = [(0,2), (2,0), (1,2), (2,1), (1,3), (3,1), (2,3), (3,2), (2,4), (4,2), (3,4), (4,3)]
    allowed_pairs = set(edges)
    
    s = Solver()
    seq = [Int(f'seq_{i}') for i in range(5)]
    start_vars = [Int(f'start_{i}') for i in range(5)]
    
    for i in range(5):
        s.add(And(seq[i] >= 0, seq[i] <= 4))
    s.add(Distinct(seq))
    
    for i in range(4):
        constraints = []
        for pair in allowed_pairs:
            a, b = pair
            constraints.append(And(seq[i] == a, seq[i+1] == b))
        s.add(Or(constraints))
    
    dur_seq = [Int(f'dur_{i}') for i in range(5)]
    for i in range(5):
        s.add(dur_seq[i] == dur_map[seq[i]])
    
    s.add(start_vars[0] == 1)
    for i in range(1,5):
        s.add(start_vars[i] == start_vars[i-1] + dur_seq[i-1] - 1)
    
    s_Riga = Int('s_Riga')
    s.add(s_Riga == Sum([If(seq[i] == 1, start_vars[i], 0) for i in range(5)]))
    s.add(Or(s_Riga == 1, s_Riga == 2))
    
    s_Istanbul = Int('s_Istanbul')
    s.add(s_Istanbul == Sum([If(seq[i] == 3, start_vars[i], 0) for i in range(5)]))
    s.add(s_Istanbul <= 7)
    
    if s.check() == sat:
        m = s.model()
        seq_val = [m[seq[i]].as_long() for i in range(5)]
        start_val = [m[start_vars[i]].as_long() for i in range(5)]
        dur_val = [dur_map[idx] for idx in seq_val]
        
        itinerary_list = []
        for i in range(5):
            city_idx = seq_val[i]
            city_name = cities[city_idx]
            start_day = start_val[i]
            end_day = start_val[i] + dur_val[i] - 1
            for day in range(start_day, end_day + 1):
                itinerary_list.append({'day': day, 'place': city_name})
        
        itinerary_list_sorted = sorted(itinerary_list, key=lambda x: x['day'])
        result = {'itinerary': itinerary_list_sorted}
        print(json.dumps(result))
    else:
        print('{"error": "No solution found"}')

if __name__ == '__main__':
    main()