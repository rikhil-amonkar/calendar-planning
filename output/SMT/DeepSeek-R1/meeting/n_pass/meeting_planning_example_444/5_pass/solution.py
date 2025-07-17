from z3 import *

def main():
    travel_time = {
        'FD': {'RH': 10, 'SD': 30, 'NB': 8, 'TC': 20, 'GG': 26},
        'RH': {'FD': 10, 'SD': 23, 'NB': 5, 'TC': 18, 'GG': 19},
        'SD': {'FD': 30, 'RH': 23, 'NB': 27, 'TC': 17, 'GG': 11},
        'NB': {'FD': 8, 'RH': 5, 'SD': 27, 'TC': 20, 'GG': 24},
        'TC': {'FD': 20, 'RH': 18, 'SD': 17, 'NB': 20, 'GG': 13},
        'GG': {'FD': 26, 'RH': 19, 'SD': 11, 'NB': 24, 'TC': 13}
    }
    
    friends = [
        ('Patricia', 'SD', 60, 15, 780),
        ('Ronald', 'RH', 105, 285, 495),
        ('Laura', 'NB', 15, 210, 225),
        ('Emily', 'TC', 60, 435, 570),
        ('Mary', 'GG', 60, 360, 450)
    ]
    
    n = len(friends)
    opt = Optimize()
    
    # Decision variables
    attend = [Bool(f"attend_{i}") for i in range(n)]
    start = [Int(f"start_{i}") for i in range(n)]
    end = [Int(f"end_{i}") for i in range(n)]
    order = [Int(f"order_{j}") for j in range(n)]
    k = Int('k')
    
    # k is number of attended meetings
    opt.add(k == Sum([If(attend[i], 1, 0) for i in range(n)]))
    
    # End time constraints
    for i, (_, _, dur, _, _) in enumerate(friends):
        opt.add(end[i] == start[i] + dur)
    
    # Availability constraints
    for i, (_, _, _, avail_start, avail_end) in enumerate(friends):
        opt.add(Implies(attend[i], And(start[i] >= avail_start, end[i] <= avail_end)))
    
    # Order array constraints
    for j in range(n):
        opt.add(Or(And(order[j] >= 0, order[j] < n, attend[order[j]]), order[j] == -1))
    
    # All attended meetings must appear exactly once in first k positions
    for i in range(n):
        opt.add(Implies(attend[i], Or([order[j] == i for j in range(n)])))
        opt.add(Implies(attend[i], Sum([If(order[j] == i, 1, 0) for j in range(n)]) == 1))
    
    # First k positions are attended meetings, rest are -1
    for j in range(n):
        opt.add(Implies(j < k, order[j] >= 0))
        opt.add(Implies(j >= k, order[j] == -1))
    
    # Distinct meetings in first k positions
    for j1 in range(n):
        for j2 in range(j1 + 1, n):
            opt.add(Implies(And(j1 < k, j2 < k), order[j1] != order[j2]))
    
    # Travel constraints
    for j in range(n):
        # First meeting: travel from FD
        if j == 0:
            for idx in range(n):
                opt.add(Implies(And(j < k, order[j] == idx),
                              start[idx] >= travel_time['FD'][friends[idx][1]]))
        # Subsequent meetings: travel from previous location
        else:
            for idx1 in range(n):
                for idx2 in range(n):
                    if idx1 != idx2:
                        cond = And(j < k, order[j-1] == idx1, order[j] == idx2)
                        loc1 = friends[idx1][1]
                        loc2 = friends[idx2][1]
                        travel = travel_time[loc1][loc2]
                        opt.add(Implies(cond, start[idx2] >= end[idx1] + travel))
    
    # Optimization objectives
    num_meetings = Sum([If(attend[i], 1, 0) for i in range(n)])
    total_start = Sum([If(attend[i], start[i], 0) for i in range(n)])
    opt.maximize(num_meetings)
    opt.minimize(total_start)
    
    # Solve and output
    if opt.check() == sat:
        model = opt.model()
        schedule = []
        for i, (name, _, _, _, _) in enumerate(friends):
            if model.evaluate(attend[i]):
                s_val = model.evaluate(start[i]).as_long()
                e_val = model.evaluate(end[i]).as_long()
                start_time = f"{9 + s_val // 60}:{s_val % 60:02d}"
                end_time = f"{9 + e_val // 60}:{e_val % 60:02d}"
                schedule.append({
                    "action": "meet",
                    "person": name,
                    "start_time": start_time,
                    "end_time": end_time
                })
        schedule.sort(key=lambda x: x["start_time"])
        print('SOLUTION:')
        print(f'{{"itinerary": {schedule}}}')
    else:
        print("No solution found")

if __name__ == '__main__':
    main()