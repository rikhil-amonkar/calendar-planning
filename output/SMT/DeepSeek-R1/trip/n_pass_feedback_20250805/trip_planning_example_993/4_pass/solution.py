from z3 import *
import json

def main():
    cities = ["Riga", "Frankfurt", "Amsterdam", "Vilnius", "London", "Stockholm", "Bucharest"]
    required_days = [2, 3, 2, 5, 2, 3, 4]
    
    directed_edges = [
        (0, 2), (2, 0),
        (0, 3),
        (0, 5), (5, 0),
        (0, 6), (6, 0),
        (1, 2), (2, 1),
        (1, 3), (3, 1),
        (1, 4), (4, 1),
        (1, 5), (5, 1),
        (1, 6), (6, 1),
        (2, 3), (3, 2),
        (2, 4), (4, 2),
        (2, 5), (5, 2),
        (2, 6), (6, 2),
        (3, 4), (4, 3),
        (4, 5), (5, 4),
        (4, 6), (6, 4),
        (5, 6), (6, 5)
    ]
    
    s = [Int(f's_{i}') for i in range(15)]
    solver = Solver()
    
    for i in range(15):
        solver.add(s[i] >= 0, s[i] < 7)
    
    solver.add(s[0] == 0)
    
    for i in range(14):
        move_cond = (s[i] != s[i+1])
        flight_ok = Or([And(s[i] == u, s[i+1] == v) for u, v in directed_edges])
        solver.add(Implies(move_cond, flight_ok))
    
    for c in range(7):
        total = 0
        for i in range(15):
            total += If(s[i] == c, 1, 0)
        solver.add(total == required_days[c])
    
    solver.add(Or(s[1] == 2, s[2] == 2))
    
    solver.add(Or(s[6] == 3, s[7] == 3, s[8] == 3, s[9] == 3, s[10] == 3))
    
    solver.add(Or(s[12] == 5, s[13] == 5, s[14] == 5))
    
    if solver.check() == sat:
        model = solver.model()
        s_val = [model.evaluate(s[i]).as_long() for i in range(15)]
        
        segments = []
        current_day = 1
        i = 0
        
        while i < 15:
            if i == 14:
                seg_start = current_day
                seg_end = current_day
                city = cities[s_val[i]]
                segments.append((seg_start, seg_end, city))
                i += 1
                current_day += 1
            else:
                if s_val[i] != s_val[i+1]:
                    seg_start = current_day
                    seg_end = current_day
                    city_str = cities[s_val[i]] + ", " + cities[s_val[i+1]]
                    segments.append((seg_start, seg_end, city_str))
                    current_day += 1
                    i += 1
                else:
                    j = i
                    while j < 15 and s_val[j] == s_val[i]:
                        j += 1
                    num_days = j - i
                    seg_start = current_day
                    seg_end = current_day + num_days - 1
                    city = cities[s_val[i]]
                    segments.append((seg_start, seg_end, city))
                    current_day = seg_end + 1
                    i = j
        
        itinerary = []
        for seg in segments:
            start, end, place = seg
            if start == end:
                day_range = f"Day {start}"
            else:
                day_range = f"Day {start}-{end}"
            itinerary.append({'day_range': day_range, 'place': place})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()