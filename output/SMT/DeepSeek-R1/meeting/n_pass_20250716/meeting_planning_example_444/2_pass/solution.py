from z3 import *

def main():
    loc_index = {
        "Financial District": 0,
        "Russian Hill": 1,
        "Sunset District": 2,
        "North Beach": 3,
        "The Castro": 4,
        "Golden Gate Park": 5
    }
    
    travel_matrix = [
        [0, 10, 31, 7, 23, 23],
        [11, 0, 23, 5, 21, 21],
        [30, 24, 0, 29, 17, 11],
        [8, 4, 27, 0, 22, 22],
        [20, 18, 17, 20, 0, 11],
        [26, 19, 10, 24, 13, 0]
    ]
    
    friends = [
        ("Ronald", "Russian Hill", (13*60 + 45, 17*60 + 15), 105),
        ("Patricia", "Sunset District", (9*60 + 15, 22*60), 60),
        ("Laura", "North Beach", (12*60 + 30, 12*60 + 45), 15),
        ("Emily", "The Castro", (16*60 + 15, 18*60 + 30), 60),
        ("Mary", "Golden Gate Park", (15*60, 16*60 + 30), 60)
    ]
    
    n = len(friends)
    opt = Optimize()
    
    meet = [Bool(f'meet_{i}') for i in range(n)]
    slot_used = [Bool(f'slot_used_{k}') for k in range(n)]
    assign = [[Bool(f'assign_{i}_{k}') for k in range(n)] for i in range(n)]
    loc = [Int(f'loc_{k}') for k in range(n)]
    start_time = [Int(f'start_time_{k}') for k in range(n)]
    end_time = [Int(f'end_time_{k}') for k in range(n)]
    travel_time = [Int(f'travel_time_{k}') for k in range(n)]
    arrival_time = [Int(f'arrival_time_{k}') for k in range(n)]
    
    for k in range(1, n):
        opt.add(Implies(slot_used[k], slot_used[k-1]))
    
    for i in range(n):
        opt.add(meet[i] == Or([assign[i][k] for k in range(n)]))
        opt.add(If(meet[i], PbEq([(assign[i][k], 1) for k in range(n)], 1), 
                  And([Not(assign[i][k]) for k in range(n)])))
    
    for k in range(n):
        opt.add(If(slot_used[k], PbEq([(assign[i][k], 1) for i in range(n)], 1),
                  And([Not(assign[i][k]) for i in range(n)])))
    
    for k in range(n):
        for i in range(n):
            opt.add(Implies(assign[i][k], loc[k] == loc_index[friends[i][1]]))
    
    for k in range(n):
        min_dur = Int(f'min_dur_{k}')
        window_start = Int(f'window_start_{k}')
        window_end = Int(f'window_end_{k}')
        for i in range(n):
            opt.add(Implies(assign[i][k], min_dur == friends[i][3]))
            opt.add(Implies(assign[i][k], window_start == friends[i][2][0]))
            opt.add(Implies(assign[i][k], window_end == friends[i][2][1]))
        opt.add(Implies(slot_used[k], 
                        And(start_time[k] >= window_start,
                            start_time[k] + min_dur <= window_end,
                            end_time[k] == start_time[k] + min_dur)))
    
    for k in range(n):
        if k == 0:
            prev_loc = 0
        else:
            prev_loc = loc[k-1]
        current_loc = loc[k]
        tt = travel_matrix[prev_loc][current_loc]
        opt.add(Implies(slot_used[k], travel_time[k] == tt))
        opt.add(Implies(Not(slot_used[k]), travel_time[k] == 0))
    
    for k in range(n):
        if k == 0:
            opt.add(arrival_time[0] == travel_time[0])
        else:
            opt.add(arrival_time[k] == end_time[k-1] + travel_time[k])
        opt.add(Implies(slot_used[k], 
                        And(arrival_time[k] <= start_time[k],
                            start_time[k] >= 0)))
    
    total_meetings = Sum([If(meet[i], 1, 0) for i in range(n)])
    opt.maximize(total_meetings)
    
    if opt.check() == sat:
        m = opt.model()
        schedule = []
        for k in range(n):
            if m.evaluate(slot_used[k]):
                for i in range(n):
                    if m.evaluate(assign[i][k]):
                        name = friends[i][0]
                        location = friends[i][1]
                        start_val = m.evaluate(start_time[k]).as_long()
                        start_hour = 9 + start_val // 60
                        start_min = start_val % 60
                        end_val = start_val + friends[i][3]
                        end_hour = 9 + end_val // 60
                        end_min = end_val % 60
                        schedule.append((k, name, location, 
                                        f"{start_hour}:{start_min:02d}", 
                                        f"{end_hour}:{end_min:02d}"))
        schedule.sort(key=lambda x: x[0])
        print("SOLUTION:")
        for slot in schedule:
            print(f"Meet {slot[1]} at {slot[2]} from {slot[3]} to {slot[4]}")
        print(f"Total meetings: {len(schedule)}")
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()