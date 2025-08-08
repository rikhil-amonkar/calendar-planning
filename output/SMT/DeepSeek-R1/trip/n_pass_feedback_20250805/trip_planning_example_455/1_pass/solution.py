from z3 import Solver, Int, Distinct, If, Or, And, sat
import json

def main():
    cities = {0: "Reykjavik", 1: "Riga", 2: "Warsaw", 3: "Istanbul", 4: "Krakow"}
    dur_map = {0: 7, 1: 2, 2: 3, 3: 6, 4: 7}
    
    edges_orig = [(0, 2), (1, 2), (1, 3), (2, 3), (2, 4), (3, 4)]
    allowed_pairs = set()
    for a, b in edges_orig:
        allowed_pairs.add((a, b))
        allowed_pairs.add((b, a))
    
    s = Solver()
    seq = [Int(f'seq_{i}') for i in range(5)]
    
    for i in range(5):
        s.add(seq[i] >= 0, seq[i] <= 4)
    s.add(Distinct(seq))
    
    for i in range(4):
        cons = []
        for pair in allowed_pairs:
            a, b = pair
            cons.append(And(seq[i] == a, seq[i+1] == b))
        s.add(Or(cons))
    
    dur_seq_vars = [Int(f'dur_seq_{i}') for i in range(5)]
    for i in range(5):
        s.add(dur_seq_vars[i] == If(seq[i] == 0, dur_map[0],
                                    If(seq[i] == 1, dur_map[1],
                                    If(seq[i] == 2, dur_map[2],
                                    If(seq[i] == 3, dur_map[3], dur_map[4])))))
    
    prefix_vars = [Int(f'prefix_{i}') for i in range(5)]
    s.add(prefix_vars[0] == dur_seq_vars[0])
    for i in range(1, 5):
        s.add(prefix_vars[i] == prefix_vars[i-1] + dur_seq_vars[i])
    
    pos_Riga = Int('pos_Riga')
    s.add(Or([And(seq[i] == 1, pos_Riga == i) for i in range(5)]))
    pos_Istanbul = Int('pos_Istanbul')
    s.add(Or([And(seq[i] == 3, pos_Istanbul == i) for i in range(5)]))
    
    s_Riga = Int('s_Riga')
    s.add(s_Riga == If(pos_Riga == 0, 1, 1 + prefix_vars[pos_Riga-1] - pos_Riga))
    s.add(s_Riga <= 2)
    
    s_Istanbul = Int('s_Istanbul')
    s.add(s_Istanbul == If(pos_Istanbul == 0, 1, 1 + prefix_vars[pos_Istanbul-1] - pos_Istanbul))
    s.add(s_Istanbul <= 7)
    
    if s.check() == sat:
        m = s.model()
        seq_val = [m[seq[i]].as_long() for i in range(5)]
        dur_seq_val = [dur_map[idx] for idx in seq_val]
        prefix_val = [0] * 5
        prefix_val[0] = dur_seq_val[0]
        for i in range(1, 5):
            prefix_val[i] = prefix_val[i-1] + dur_seq_val[i]
        start_days = [1] + [1 + prefix_val[i-1] - i for i in range(1, 5)]
        end_days = [start_days[i] + dur_seq_val[i] - 1 for i in range(5)]
        
        itinerary = []
        for i in range(5):
            city_name = cities[seq_val[i]]
            for day in range(start_days[i], end_days[i] + 1):
                itinerary.append({'day': day, 'place': city_name})
        
        itinerary_sorted = sorted(itinerary, key=lambda x: x['day'])
        result = {'itinerary': itinerary_sorted}
        print(json.dumps(result))
    else:
        print('{"error": "No solution found"}')

if __name__ == '__main__':
    main()