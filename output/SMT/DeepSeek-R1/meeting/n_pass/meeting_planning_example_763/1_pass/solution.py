from z3 import *

def main():
    # Travel matrix: [from][to] 
    # Indices: 0:Embarcadero, 1:Pacific Heights, 2:Russian Hill, 3:Haight-Ashbury, 
    #          4:Golden Gate Park, 5:Fisherman's Wharf, 6:Sunset District, 7:The Castro, 8:Chinatown
    travel = [
        [0, 11, 8, 21, 25, 6, 30, 25, 7],
        [10, 0, 7, 11, 15, 13, 21, 16, 11],
        [8, 7, 0, 17, 21, 7, 23, 21, 9],
        [20, 12, 17, 0, 7, 23, 15, 6, 19],
        [25, 16, 19, 7, 0, 24, 10, 13, 23],
        [8, 12, 7, 22, 25, 0, 27, 27, 12],
        [30, 21, 24, 15, 11, 29, 0, 17, 30],
        [22, 16, 18, 6, 11, 24, 17, 0, 22],
        [5, 10, 7, 19, 23, 8, 29, 22, 0]
    ]
    
    friends = [
        # (window_start, window_end, min_duration)
        (375, 585, 90),  # Richard (0: Embarcadero)
        (360, 480, 45),   # Mark (1: Pacific Heights)
        (510, 720, 90),   # Matthew (2: Russian Hill)
        (345, 540, 60),   # Rebecca (3: Haight-Ashbury)
        (285, 510, 90),   # Melissa (4: Golden Gate Park)
        (345, 675, 15),   # Margaret (5: Fisherman's Wharf)
        (405, 480, 45),   # Emily (6: Sunset District)
        (300, 435, 75)    # George (7: The Castro)
    ]
    
    s = [Int(f's_{i}') for i in range(8)]
    meet = [Bool(f'meet_{i}') for i in range(8)]
    order = [Int(f'order_{i}') for i in range(8)]
    
    solver = Optimize()
    
    # Constraint: If meeting a friend, their start time must be at least travel time from Chinatown and within their window
    for i in range(8):
        solver.add(Implies(meet[i], s[i] >= travel[8][i]))
        solver.add(Implies(meet[i], s[i] >= friends[i][0]))
        solver.add(Implies(meet[i], s[i] + friends[i][2] <= friends[i][1]))
        solver.add(Implies(meet[i], And(order[i] >= 0, order[i] <= 7)))
    
    # Constraint: Distinct orders for friends met
    for i in range(8):
        for j in range(i+1, 8):
            solver.add(Implies(And(meet[i], meet[j]), order[i] != order[j]))
    
    # Constraint: If two friends are met, ensure travel time and meeting duration are respected based on order
    for i in range(8):
        for j in range(8):
            if i == j:
                continue
            cond1 = And(meet[i], meet[j], order[i] < order[j], 
                        s[j] >= s[i] + friends[i][2] + travel[i][j])
            cond2 = And(meet[i], meet[j], order[i] > order[j], 
                        s[i] >= s[j] + friends[j][2] + travel[j][i])
            solver.add(Or(cond1, cond2, Not(And(meet[i], meet[j]))))
    
    # Objective: Maximize number of friends met
    total_meet = Sum([If(meet_i, 1, 0) for meet_i in meet])
    solver.maximize(total_meet)
    
    # Solve and output results
    if solver.check() == sat:
        model = solver.model()
        total_met = sum(1 for i in range(8) if is_true(model.eval(meet[i])))
        print(f"Total friends met: {total_met}")
        
        schedule = []
        for i in range(8):
            if is_true(model.eval(meet[i])):
                start_val = model.eval(s[i]).as_long()
                order_val = model.eval(order[i]).as_long()
                start_hour = 9 + start_val // 60
                start_minute = start_val % 60
                end_time = start_val + friends[i][2]
                end_hour = 9 + end_time // 60
                end_minute = end_time % 60
                schedule.append((i, order_val, start_val, start_hour, start_minute, end_hour, end_minute))
        
        schedule.sort(key=lambda x: x[2])
        
        friend_names = [
            "Richard (Embarcadero)",
            "Mark (Pacific Heights)",
            "Matthew (Russian Hill)",
            "Rebecca (Haight-Ashbury)",
            "Melissa (Golden Gate Park)",
            "Margaret (Fisherman's Wharf)",
            "Emily (Sunset District)",
            "George (The Castro)"
        ]
        
        print("Schedule in order of start time:")
        for (i, order_val, start_val, start_hour, start_minute, end_hour, end_minute) in schedule:
            print(f"Meet {friend_names[i]} from {int(start_hour)}:{start_minute:02d} to {int(end_hour)}:{end_minute:02d} (order: {order_val})")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()