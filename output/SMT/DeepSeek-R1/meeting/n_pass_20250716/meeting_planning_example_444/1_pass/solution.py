from z3 import *

def main():
    # Define location indices
    loc_index = {
        "Financial District": 0,
        "Russian Hill": 1,
        "Sunset District": 2,
        "North Beach": 3,
        "The Castro": 4,
        "Golden Gate Park": 5
    }
    
    # Define travel time matrix (6x6)
    travel_matrix = [
        [0, 10, 31, 7, 23, 23],
        [11, 0, 23, 5, 21, 21],
        [30, 24, 0, 29, 17, 11],
        [8, 4, 27, 0, 22, 22],
        [20, 18, 17, 20, 0, 11],
        [26, 19, 10, 24, 13, 0]
    ]
    
    # Define friends: (name, location, (start_min, end_min), min_duration)
    friends = [
        ("Ronald", "Russian Hill", (285, 495), 105),
        ("Patricia", "Sunset District", (15, 780), 60),
        ("Laura", "North Beach", (210, 225), 15),
        ("Emily", "The Castro", (435, 570), 60),
        ("Mary", "Golden Gate Park", (360, 450), 60)
    ]
    
    n = len(friends)  # Number of friends
    
    s = Solver()
    
    # used[k] = True if slot k is used
    used = [Bool('used_%d' % k) for k in range(n)]
    # assign[i][k] = True if friend i is assigned to slot k
    assign = [[Bool('assign_%d_%d' % (i, k)) for k in range(n)] for i in range(n)]
    
    # Constraint: used must be contiguous (prefix-based)
    for k in range(1, n):
        s.add(Implies(used[k], used[k-1]))
    
    # Constraints for each friend: if met, assigned to exactly one slot; else not assigned to any
    for i in range(n):
        meet_i = Or([assign[i][k] for k in range(n)])
        s.add(If(meet_i, 
                 PbEq([(assign[i][k], 1) for k in range(n)], 1),
                 And([Not(assign[i][k]) for k in range(n)])))
    
    # Constraints for each slot: if used, exactly one friend assigned; else none
    for k in range(n):
        s.add(If(used[k],
                 PbEq([(assign[i][k], 1) for i in range(n)], 1),
                 And([Not(assign[i][k]) for i in range(n)])))
    
    # Location for each slot
    loc = [Int('loc_%d' % k) for k in range(n)]
    for k in range(n):
        for i in range(n):
            s.add(Implies(assign[i][k], loc[k] == loc_index[friends[i][1]]))
    
    # min_time_k, friend_start_k, friend_end_k for each slot
    min_time_k = [Int('min_time_%d' % k) for k in range(n)]
    friend_start_k = [Int('friend_start_%d' % k) for k in range(n)]
    friend_end_k = [Int('friend_end_%d' % k) for k in range(n)]
    
    for k in range(n):
        expr_min = 0
        expr_start = 0
        expr_end = 0
        for i in range(n):
            expr_min = If(assign[i][k], friends[i][3], expr_min)
            expr_start = If(assign[i][k], friends[i][2][0], expr_start)
            expr_end = If(assign[i][k], friends[i][2][1], expr_end)
        s.add(min_time_k[k] == expr_min)
        s.add(friend_start_k[k] == expr_start)
        s.add(friend_end_k[k] == expr_end)
    
    # Travel time for each slot
    travel_time = [Int('travel_time_%d' % k) for k in range(n)]
    # Slot 0: from Financial District (0) to loc[0]
    expr_t0 = 0
    for j in range(1, 6):
        expr_t0 = If(And(used[0], loc[0] == j), travel_matrix[0][j], expr_t0)
    s.add(travel_time[0] == expr_t0)
    # Slots 1 to 4: from loc[k-1] to loc[k]
    for k in range(1, n):
        expr_t = 0
        for i in range(1, 6):
            for j in range(1, 6):
                expr_t = If(And(used[k], loc[k-1] == i, loc[k] == j), travel_matrix[i][j], expr_t)
        s.add(travel_time[k] == expr_t)
    
    # Time variables (in minutes from 9:00 AM)
    arrival = [Int('arrival_%d' % k) for k in range(n)]
    start = [Int('start_%d' % k) for k in range(n)]
    departure = [Int('departure_%d' % k) for k in range(n)]
    
    # Slot 0 constraints
    s.add(arrival[0] == travel_time[0])
    s.add(If(used[0],
             And(
                 start[0] >= arrival[0],
                 start[0] >= friend_start_k[0],
                 start[0] <= friend_end_k[0] - min_time_k[0],
                 departure[0] == start[0] + min_time_k[0]
             ),
             departure[0] == 0))
    
    # Slots 1 to 4 constraints
    for k in range(1, n):
        s.add(arrival[k] == departure[k-1] + travel_time[k])
        s.add(If(used[k],
                 And(
                     start[k] >= arrival[k],
                     start[k] >= friend_start_k[k],
                     start[k] <= friend_end_k[k] - min_time_k[k],
                     departure[k] == start[k] + min_time_k[k]
                 ),
                 departure[k] == departure[k-1]))
    
    # Objective: maximize number of meetings
    total_meetings = Sum([If(used[k], 1, 0) for k in range(n)])
    s.maximize(total_meetings)
    
    # Solve and output
    if s.check() == sat:
        m = s.model()
        total = 0
        schedule = []
        for k in range(n):
            if is_true(m.evaluate(used[k])):
                total += 1
                for i in range(n):
                    if is_true(m.evaluate(assign[i][k])):
                        friend_name = friends[i][0]
                        loc_name = friends[i][1]
                        start_min = m.evaluate(start[k]).as_long()
                        # Convert to time string
                        total_minutes = start_min
                        hours = total_minutes // 60
                        minutes = total_minutes % 60
                        start_time = f"{9 + hours}:{minutes:02d}"
                        end_min = start_min + friends[i][3]
                        hours_end = end_min // 60
                        minutes_end = end_min % 60
                        end_time = f"{9 + hours_end}:{minutes_end:02d}"
                        schedule.append((k, friend_name, loc_name, start_time, end_time))
        # Sort by slot order
        schedule.sort(key=lambda x: x[0])
        print("SOLUTION:")
        for slot in schedule:
            print(f"Meet {slot[1]} at {slot[2]} from {slot[3]} to {slot[4]}")
        print(f"Total meetings: {total}")
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()