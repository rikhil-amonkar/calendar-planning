from z3 import *

def main():
    # Travel time matrix (7x7) for locations: 
    # 0: Financial District, 1: Golden Gate Park, 2: Chinatown, 3: Union Square, 
    # 4: Fisherman's Wharf, 5: Pacific Heights, 6: North Beach
    travel_time = [
        [0, 23, 5, 9, 10, 13, 7],   # from 0 (Financial District)
        [26, 0, 23, 22, 24, 16, 24], # from 1 (Golden Gate Park)
        [5, 23, 0, 7, 8, 10, 3],    # from 2 (Chinatown)
        [9, 22, 7, 0, 15, 15, 10],  # from 3 (Union Square)
        [11, 25, 12, 13, 0, 12, 6], # from 4 (Fisherman's Wharf)
        [13, 15, 11, 12, 13, 0, 9], # from 5 (Pacific Heights)
        [8, 22, 6, 7, 5, 8, 0]      # from 6 (North Beach)
    ]
    
    # Friends data: (location, available_start, available_end, min_duration)
    # Index: 
    # 0: Stephanie (Golden Gate Park)
    # 1: Karen (Chinatown)
    # 2: Brian (Union Square)
    # 3: Rebecca (Fisherman's Wharf)
    # 4: Joseph (Pacific Heights)
    # 5: Steven (North Beach)
    friends = [
        (1, 120, 360, 105),  # Stephanie: 11:00 AM to 3:00 PM, min 105 min
        (2, 285, 450, 15),   # Karen: 1:45 PM to 4:30 PM, min 15 min
        (3, 360, 495, 30),   # Brian: 3:00 PM to 5:15 PM, min 30 min
        (4, 0, 135, 30),     # Rebecca: 9:00 AM to 11:15 AM, min 30 min
        (5, 0, 30, 60),      # Joseph: 9:00 AM to 9:30 AM, min 60 min (impossible)
        (6, 330, 705, 120)   # Steven: 2:30 PM to 8:45 PM, min 120 min
    ]
    
    n = len(friends)  # 6 friends
    
    # Create Z3 variables
    meet = [Bool('meet_%d' % i) for i in range(n)]
    start = [Real('start_%d' % i) for i in range(n)]
    end = [Real('end_%d' % i) for i in range(n)]
    # before[i][j] means meeting i is before meeting j (for i != j)
    before = [[Bool('before_%d_%d' % (i, j)) for j in range(n)] for i in range(n)]
    
    s = Solver()
    
    # Friend-specific constraints
    for i in range(n):
        loc_i = friends[i][0]
        avail_start = friends[i][1]
        avail_end = friends[i][2]
        min_dur = friends[i][3]
        
        # If we meet friend i, then the meeting must be within availability and at least min_dur
        s.add(If(meet[i],
                 And(start[i] >= avail_start,
                     end[i] == start[i] + min_dur,
                     end[i] <= avail_end),
                 True))
        
        # Any meeting that happens must start at least after the travel time from start location (Financial District)
        s.add(Implies(meet[i], start[i] >= travel_time[0][loc_i]))
        
        # For every other meeting j that is before i, add travel constraint
        for j in range(n):
            if i == j:
                continue
            loc_j = friends[j][0]
            s.add(Implies(And(meet[i], meet[j], before[j][i]),
                          start[i] >= end[j] + travel_time[loc_j][loc_i]))
    
    # Order constraints: antisymmetry and transitivity
    for i in range(n):
        for j in range(n):
            if i == j:
                continue
            # Antisymmetry: if both i and j are met, then exactly one of before[i][j] or before[j][i] is true
            s.add(Implies(And(meet[i], meet[j]), 
                          Xor(before[i][j], before[j][i])))
            
            # Transitivity for every trio (i, j, k)
            for k in range(n):
                if i == k or j == k:
                    continue
                s.add(Implies(And(meet[i], meet[j], meet[k]),
                              Implies(And(before[i][j], before[j][k]), before[i][k])))
    
    # Maximize the number of meetings
    num_meetings = Sum([If(meet[i], 1, 0) for i in range(n)])
    s.maximize(num_meetings)
    
    # Check and get the model
    if s.check() == sat:
        model = s.model()
        total_meetings = 0
        schedule = []
        for i in range(n):
            if is_true(model.eval(meet[i])):
                total_meetings += 1
                s_val = model.eval(start[i])
                e_val = model.eval(end[i])
                # Convert Z3 values to integers
                s_min = s_val.numerator_as_long() // s_val.denominator_as_long() if is_rational_value(s_val) else int(str(s_val))
                e_min = e_val.numerator_as_long() // e_val.denominator_as_long() if is_rational_value(e_val) else int(str(e_val))
                # Convert minutes to time
                start_time = (9 * 60 + s_min) % (24 * 60)
                end_time = (9 * 60 + e_min) % (24 * 60)
                start_str = f"{start_time // 60}:{start_time % 60:02d}"
                end_str = f"{end_time // 60}:{end_time % 60:02d}"
                friend_names = ['Stephanie', 'Karen', 'Brian', 'Rebecca', 'Joseph', 'Steven']
                schedule.append((friend_names[i], start_str, end_str))
        # Print the schedule
        print(f"Total meetings: {total_meetings}")
        for name, start, end in schedule:
            print(f"Meet {name} from {start} to {end}")
    else:
        print("No solution found")

if __name__ == '__main__':
    main()