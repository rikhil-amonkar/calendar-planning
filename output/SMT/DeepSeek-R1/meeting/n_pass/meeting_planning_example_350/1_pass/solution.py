from z3 import *

def main():
    # Travel times matrix: [Bayview, Pacific Heights, Mission District, Haight-Ashbury, Financial District]
    travel = [
        [0, 23, 13, 19, 19],   # Bayview (0) to others
        [22, 0, 15, 11, 13],    # Pacific Heights (1) to others
        [15, 16, 0, 12, 17],    # Mission District (2) to others
        [18, 12, 11, 0, 21],    # Haight-Ashbury (3) to others
        [19, 13, 17, 19, 0]     # Financial District (4) to others
    ]
    
    base_time = 540  # 9:00 AM in minutes from midnight
    
    friends = [
        {'name': 'Betty', 'loc': 3, 'dur': 90, 'start_avail': 435, 'end_avail': 1035},  # 7:15 AM to 5:15 PM
        {'name': 'Mary', 'loc': 1, 'dur': 45, 'start_avail': 600, 'end_avail': 1140},    # 10:00 AM to 7:00 PM
        {'name': 'Charles', 'loc': 4, 'dur': 120, 'start_avail': 675, 'end_avail': 900},  # 11:15 AM to 3:00 PM
        {'name': 'Lisa', 'loc': 2, 'dur': 75, 'start_avail': 1230, 'end_avail': 1320}     # 8:30 PM to 10:00 PM
    ]
    n = len(friends)
    
    meet = [Bool(f"meet_{i}") for i in range(n)]
    start = [Int(f"start_{i}") for i in range(n)]
    
    s = Solver()
    
    for i in range(n):
        min_start_avail = max(base_time, friends[i]['start_avail'])
        min_start_travel = base_time + travel[0][friends[i]['loc']]
        min_start = max(min_start_avail, min_start_travel)
        
        s.add(Implies(meet[i], start[i] >= min_start))
        s.add(Implies(meet[i], start[i] + friends[i]['dur'] <= friends[i]['end_avail']))
    
    for i in range(n):
        for j in range(i+1, n):
            if i != j:
                loc_i = friends[i]['loc']
                loc_j = friends[j]['loc']
                travel_ij = travel[loc_i][loc_j]
                travel_ji = travel[loc_j][loc_i]
                
                constraint1 = (start[i] + friends[i]['dur'] + travel_ij <= start[j])
                constraint2 = (start[j] + friends[j]['dur'] + travel_ji <= start[i])
                
                s.add(Implies(And(meet[i], meet[j]), Or(constraint1, constraint2)))
    
    opt = Optimize()
    opt.add(s.assertions())
    total_meet = Sum([If(meet[i], 1, 0) for i in range(n)])
    opt.maximize(total_meet)
    
    if opt.check() == sat:
        m = opt.model()
        total = 0
        result = []
        for i in range(n):
            is_met = m.eval(meet[i])
            if is_met:
                total += 1
                start_val = m.eval(start[i])
                if isinstance(start_val, IntNumRef):
                    start_min = start_val.as_long()
                else:
                    start_min = start_val
                hours = start_min // 60
                minutes = start_min % 60
                time_str = f"{hours}:{minutes:02d}"
                result.append(f"Meet {friends[i]['name']} at {time_str}")
            else:
                result.append(f"Skip {friends[i]['name']}")
        result.append(f"Total meetings: {total}")
        print("\n".join(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()