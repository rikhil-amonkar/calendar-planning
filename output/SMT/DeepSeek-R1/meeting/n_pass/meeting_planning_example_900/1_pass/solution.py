from z3 import *

def main():
    n = 11  # 11 meetings: 0 (start) + 10 friends
    districts = [
        "Richmond District",   #0
        "The Castro",           #1
        "Nob Hill",             #2
        "Marina District",      #3
        "Pacific Heights",      #4
        "Haight-Ashbury",       #5
        "Mission District",     #6
        "Chinatown",            #7
        "Russian Hill",         #8
        "Alamo Square",         #9
        "Bayview"               #10
    ]
    
    # Travel time matrix T: 11x11, T[i][j] = travel time from district i to district j
    T = [
        [0, 16, 17, 9, 10, 10, 20, 20, 13, 13, 27],   #0: Richmond
        [16, 0, 16, 21, 16, 6, 7, 22, 18, 8, 19],     #1: The Castro
        [14, 17, 0, 11, 8, 13, 13, 6, 5, 11, 19],     #2: Nob Hill
        [11, 22, 12, 0, 7, 16, 20, 15, 8, 15, 27],    #3: Marina District
        [12, 16, 8, 6, 0, 11, 15, 11, 7, 10, 22],     #4: Pacific Heights
        [10, 6, 15, 17, 12, 0, 11, 19, 17, 5, 18],    #5: Haight-Ashbury
        [20, 7, 12, 19, 16, 12, 0, 16, 15, 11, 14],   #6: Mission District
        [20, 22, 9, 12, 10, 19, 17, 0, 7, 17, 20],    #7: Chinatown
        [14, 21, 5, 7, 7, 17, 16, 9, 0, 15, 23],      #8: Russian Hill
        [11, 8, 11, 15, 10, 5, 10, 15, 13, 0, 16],    #9: Alamo Square
        [25, 19, 20, 27, 23, 19, 13, 19, 23, 16, 0]   #10: Bayview
    ]
    
    # Availability and minimum meeting times for meetings 1 to 10 (0 is dummy start)
    available_start = [0] * n
    available_end = [0] * n
    min_time_arr = [0] * n
    
    # Meeting 1: Matthew (The Castro)
    available_start[1] = 16*60 + 30  # 4:30 PM
    available_end[1] = 20*60        # 8:00 PM
    min_time_arr[1] = 45
    
    # Meeting 2: Rebecca (Nob Hill)
    available_start[2] = 15*60 + 15  # 3:15 PM
    available_end[2] = 19*60 + 15    # 7:15 PM
    min_time_arr[2] = 105
    
    # Meeting 3: Brian (Marina District)
    available_start[3] = 14*60 + 15  # 2:15 PM
    available_end[3] = 22*60         # 10:00 PM
    min_time_arr[3] = 30
    
    # Meeting 4: Emily (Pacific Heights)
    available_start[4] = 11*60 + 15  # 11:15 AM
    available_end[4] = 19*60 + 45    # 7:45 PM
    min_time_arr[4] = 15
    
    # Meeting 5: Karen (Haight-Ashbury)
    available_start[5] = 11*60 + 45  # 11:45 AM
    available_end[5] = 17*60 + 30    # 5:30 PM
    min_time_arr[5] = 30
    
    # Meeting 6: Stephanie (Mission District)
    available_start[6] = 13*60       # 1:00 PM
    available_end[6] = 15*60 + 45    # 3:45 PM
    min_time_arr[6] = 75
    
    # Meeting 7: James (Chinatown)
    available_start[7] = 14*60 + 30  # 2:30 PM
    available_end[7] = 19*60         # 7:00 PM
    min_time_arr[7] = 120
    
    # Meeting 8: Steven (Russian Hill)
    available_start[8] = 14*60       # 2:00 PM
    available_end[8] = 20*60         # 8:00 PM
    min_time_arr[8] = 30
    
    # Meeting 9: Elizabeth (Alamo Square)
    available_start[9] = 13*60       # 1:00 PM
    available_end[9] = 17*60 + 15    # 5:15 PM
    min_time_arr[9] = 120
    
    # Meeting 10: William (Bayview)
    available_start[10] = 18*60 + 15 # 6:15 PM
    available_end[10] = 20*60 + 15   # 8:15 PM
    min_time_arr[10] = 90
    
    # Create Z3 variables and solver
    meet = [None] * n
    start = [None] * n
    end = [None] * n
    order = [None] * n
    
    # Meeting 0: fixed start at Richmond at 9:00 AM (540 minutes)
    meet[0] = True
    start[0] = 540
    end[0] = 540
    order[0] = 0
    
    # Initialize variables for meetings 1 to 10
    for i in range(1, n):
        meet[i] = Bool(f'meet_{i}')
        start[i] = Int(f'start_{i}')
        end[i] = Int(f'end_{i}')
        order[i] = Int(f'order_{i}')
    
    opt = Optimize()
    
    # Add constraints for meetings 1 to 10
    for i in range(1, n):
        # If meeting i is scheduled, it must be within availability and meet min duration
        opt.add(If(meet[i], start[i] >= available_start[i], True))
        opt.add(If(meet[i], end[i] == start[i] + min_time_arr[i], True))
        opt.add(If(meet[i], end[i] <= available_end[i], True))
        # If meeting i is scheduled, its order must be between 1 and 10
        opt.add(If(meet[i], And(order[i] >= 1, order[i] <= 10), True))
    
    # Distinct orders for all scheduled meetings
    for i in range(n):
        for j in range(i+1, n):
            # If both meetings i and j are scheduled, their orders must be different
            opt.add(If(And(meet[i], meet[j]), order[i] != order[j], True))
    
    # Order and travel time constraints
    for i in range(n):
        for j in range(n):
            if i == j:
                continue
            # If both meetings are scheduled and i comes before j, add travel time constraint
            opt.add(If(And(meet[i], meet[j]),
                        If(order[i] < order[j], 
                           end[i] + T[i][j] <= start[j], 
                           True),
                        True))
    
    # Maximize the number of scheduled meetings (excluding the start)
    total_meet = Sum([If(meet[i], 1, 0) for i in range(1, n)])
    opt.maximize(total_meet)
    
    # Solve and print results
    if opt.check() == sat:
        m = opt.model()
        total = m.evaluate(total_meet)
        print(f"Total friends met: {total}")
        for i in range(1, n):
            if m.evaluate(meet[i]):
                s_val = m.evaluate(start[i]).as_long()
                e_val = m.evaluate(end[i]).as_long()
                s_hour = s_val // 60
                s_min = s_val % 60
                e_hour = e_val // 60
                e_min = e_val % 60
                print(f"Meet {districts[i]}: from {s_hour}:{s_min:02d} to {e_hour}:{e_min:02d}")
            else:
                print(f"Did not meet {districts[i]}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()