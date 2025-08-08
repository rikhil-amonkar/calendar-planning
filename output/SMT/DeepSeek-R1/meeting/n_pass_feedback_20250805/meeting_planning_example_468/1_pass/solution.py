import itertools
import json
from z3 import *

def main():
    T = [
        [0, 19, 16, 8, 24, 11],
        [20, 0, 23, 16, 25, 22],
        [16, 22, 0, 10, 13, 15],
        [8, 16, 10, 0, 19, 9],
        [26, 26, 12, 20, 0, 25],
        [13, 23, 16, 10, 24, 0]
    ]
    
    friends = ["Rebecca", "Amanda", "James", "Sarah", "Melissa"]
    locs = [1, 2, 3, 4, 5]
    min_start = [0, 570, 45, 0, 0]
    max_end = [225, 765, 735, 750, 585]
    
    for k in range(5, 0, -1):
        for C in itertools.combinations(range(5), k):
            s = Solver()
            order = [Int(f'order_{i}') for i in range(k)]
            for i in range(k):
                s.add(order[i] >= 0, order[i] < k)
            s.add(Distinct(order))
            
            start_times = [Int(f'start_{i}') for i in range(k)]
            
            locs_C = [locs[i] for i in C]
            min_start_C = [min_start[i] for i in C]
            max_end_C = [max_end[i] for i in C]
            
            travel0_options = [T[0][locs_C[j]] for j in range(k)]
            travel0 = travel0_options[0]
            for j in range(1, k):
                travel0 = If(order[0] == j, travel0_options[j], travel0)
            s.add(start_times[0] == travel0)
            
            if k > 1:
                travel_C = [[T[locs_C[i]][locs_C[j]] for j in range(k)] for i in range(k)]
                for i in range(1, k):
                    travel_time = 0
                    for prev_idx in range(k):
                        for curr_idx in range(k):
                            travel_time = If(And(order[i-1] == prev_idx, order[i] == curr_idx),
                                            travel_C[prev_idx][curr_idx],
                                            travel_time)
                    s.add(start_times[i] == start_times[i-1] + 90 + travel_time)
            
            for i in range(k):
                min_val = min_start_C[0]
                for j in range(1, k):
                    min_val = If(order[i] == j, min_start_C[j], min_val)
                s.add(start_times[i] >= min_val)
                
                max_val = max_end_C[0]
                for j in range(1, k):
                    max_val = If(order[i] == j, max_end_C[j], max_val)
                s.add(start_times[i] + 90 <= max_val)
            
            if s.check() == sat:
                m = s.model()
                meetings = []
                for i in range(k):
                    ord_i = m.evaluate(order[i]).as_long()
                    friend_idx = C[ord_i]
                    start_val = m.evaluate(start_times[i])
                    if is_int_value(start_val):
                        start_minutes = start_val.as_long()
                    else:
                        start_minutes = int(str(start_val))
                    total_minutes = start_minutes
                    hours = 9 + total_minutes // 60
                    minutes = total_minutes % 60
                    start_time_str = f"{hours:02d}:{minutes:02d}"
                    
                    end_minutes = start_minutes + 90
                    end_hours = 9 + end_minutes // 60
                    end_minutes %= 60
                    end_time_str = f"{end_hours:02d}:{end_minutes:02d}"
                    
                    person = friends[friend_idx]
                    meetings.append((start_time_str, end_time_str, person))
                
                meetings_sorted = sorted(meetings, key=lambda x: x[0])
                itinerary = []
                for start, end, person in meetings_sorted:
                    itinerary.append({
                        "action": "meet",
                        "person": person,
                        "start_time": start,
                        "end_time": end
                    })
                
                print("SOLUTION:")
                print(json.dumps({"itinerary": itinerary}))
                return
    
    print("SOLUTION:")
    print(json.dumps({"itinerary": []}))

def is_int_value(v):
    return isinstance(v, IntNumRef)

if __name__ == "__main__":
    main()