from z3 import *
import json

def main():
    friends = [
        ("Laura", 1, 870, 975, 75),   # (name, location_index, available_start, available_end, min_duration)
        ("Brian", 2, 615, 1020, 30),
        ("Karen", 3, 1080, 1215, 90),
        ("Stephanie", 4, 615, 960, 75),
        ("Helen", 5, 690, 1305, 120),
        ("Sandra", 6, 540, 915, 30),
        ("Mary", 7, 1005, 1125, 120),
        ("Deborah", 8, 1140, 1245, 105),
        ("Elizabeth", 9, 540, 795, 105)
    ]
    
    travel = [
        [0, 11, 25, 15, 17, 17, 20, 19, 15, 19],
        [10, 0, 17, 13, 15, 9, 11, 16, 17, 15],
        [26, 19, 0, 14, 18, 12, 7, 20, 23, 11],
        [16, 15, 14, 0, 5, 21, 14, 8, 11, 7],
        [18, 16, 17, 4, 0, 22, 18, 6, 8, 9],
        [17, 9, 11, 19, 23, 0, 7, 25, 26, 16],
        [20, 13, 7, 13, 17, 9, 0, 19, 22, 9],
        [20, 19, 20, 8, 5, 25, 21, 0, 5, 12],
        [17, 17, 22, 11, 7, 23, 21, 4, 0, 15],
        [20, 15, 10, 8, 11, 18, 11, 14, 17, 0]
    ]
    
    s = Solver()
    n = len(friends)
    scheduled = [Bool(f'scheduled_{i}') for i in range(n)]
    start_time = [Int(f'start_{i}') for i in range(n)]
    end_time = [Int(f'end_{i}') for i in range(n)]
    position = [Int(f'pos_{i}') for i in range(n)]
    
    m = Sum([If(scheduled[i], 1, 0) for i in range(n)])
    
    for i in range(n):
        s.add(If(scheduled[i], And(position[i] >= 1, position[i] <= n), position[i] == 0))
    
    for i in range(n):
        for j in range(i+1, n):
            s.add(If(And(scheduled[i], scheduled[j]), position[i] != position[j], True))
    
    for k in range(1, n+1):
        count = Sum([If(And(scheduled[i], position[i] == k), 1, 0) for i in range(n)])
        s.add(count == If(k <= m, 1, 0))
    
    for i in range(n):
        name_i, loc_i, avail_start_i, avail_end_i, dur_i = friends[i]
        arrival_time_i = Int(f'arrival_{i}')
        if scheduled[i]:
            cond = (position[i] == 1)
            then_val = 540 + travel[0][loc_i]
            else_val = 0
            for j in range(n):
                _, loc_j, _, _, _ = friends[j]
                else_val = else_val + If(And(scheduled[j], position[j] == position[i] - 1), 
                                         end_time[j] + travel[loc_j][loc_i], 0)
            s.add(arrival_time_i == If(cond, then_val, else_val))
            s.add(start_time[i] >= arrival_time_i)
            s.add(start_time[i] >= avail_start_i)
            s.add(end_time[i] == start_time[i] + dur_i)
            s.add(end_time[i] <= avail_end_i)
        else:
            s.add(arrival_time_i == 0)
    
    opt = Optimize()
    opt.add(s.assertions())
    opt.maximize(m)
    
    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        for i in range(n):
            if is_true(model.eval(scheduled[i])):
                start_val = model.eval(start_time[i])
                end_val = model.eval(end_time[i])
                start_min = start_val.as_long()
                end_min = end_val.as_long()
                start_hour = start_min // 60
                start_minute = start_min % 60
                end_hour = end_min // 60
                end_minute = end_min % 60
                start_str = f"{start_hour:02d}:{start_minute:02d}"
                end_str = f"{end_hour:02d}:{end_minute:02d}"
                itinerary.append({
                    "action": "meet",
                    "person": friends[i][0],
                    "start_time": start_str,
                    "end_time": end_str
                })
        itinerary_sorted = sorted(itinerary, key=lambda x: x['start_time'])
        print('SOLUTION:')
        print(json.dumps({"itinerary": itinerary_sorted}))
    else:
        print('SOLUTION:')
        print(json.dumps({"itinerary": []}))

if __name__ == '__main__':
    main()