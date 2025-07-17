from z3 import *

def main():
    # Define meetings: index to name mapping
    meeting_names = {
        0: "Charles (Alamo Square)",
        1: "Margaret (Russian Hill)",
        2: "Daniel (Golden Gate Park)",
        3: "Stephanie (Mission District)"
    }
    
    # Locations: 
    #   0: Sunset District
    #   1: Alamo Square
    #   2: Russian Hill
    #   3: Golden Gate Park
    #   4: Mission District
    loc_map = {
        0: 1,   # Charles: Alamo Square (1)
        1: 2,   # Margaret: Russian Hill (2)
        2: 3,   # Daniel: Golden Gate Park (3)
        3: 4    # Stephanie: Mission District (4)
    }
    
    # Travel times matrix: [from][to] -> minutes
    travel_times = [
        [0, 17, 24, 11, 24],   # from Sunset (0)
        [16, 0, 13, 9, 10],    # from Alamo (1)
        [23, 15, 0, 21, 16],   # from Russian (2)
        [10, 10, 19, 0, 17],   # from GoldenGate (3)
        [24, 11, 15, 17, 0]    # from Mission (4)
    ]
    
    # Time windows in minutes from 9:00 AM (0 minutes = 9:00 AM)
    window_start = [540, 0, 0, 690]   # [Charles, Margaret, Daniel, Stephanie]
    window_end   = [705, 420, 270, 780] 
    min_duration = [90, 30, 15, 90]   # minimum meeting durations in minutes
    
    n_meetings = 4
    n_positions = 4   # maximum positions in the sequence
    
    # Declare variables
    do = [Bool('do_%d' % i) for i in range(n_meetings)]
    order = [Int('order_%d' % j) for j in range(n_positions)]
    start = [Int('start_%d' % i) for i in range(n_meetings)]
    end   = [Int('end_%d' % i) for i in range(n_meetings)]
    
    s = Solver()
    
    # Constraints for order: each order[j] is in [-1, 3]
    for j in range(n_positions):
        s.add(order[j] >= -1)
        s.add(order[j] < n_meetings)  # so order[j] <= 3 (since n_meetings=4, so <4 means 0,1,2,3 or -1)
    
    # active[j] is True if order[j] >=0
    active = [order[j] >= 0 for j in range(n_positions)]
    
    # Active positions must be consecutive starting from 0
    for j in range(n_positions-1):
        s.add(Implies(Not(active[j]), Not(active[j+1])))
    
    # Each meeting that is done appears exactly once in the order
    for i in range(n_meetings):
        # do[i] is true iff there exists j with order[j] == i
        s.add(do[i] == Or([order[j] == i for j in range(n_positions)]))
    
    # If active, then the meeting index must be valid and distinct
    for j in range(n_positions):
        for k in range(j+1, n_positions):
            s.add(Implies(And(active[j], active[k]), order[j] != order[k]))
    
    # Time window and duration constraints for each meeting if done
    for i in range(n_meetings):
        s.add(Implies(do[i], 
                      And(start[i] >= window_start[i],
                          end[i] == start[i] + min_duration[i],
                          end[i] <= window_end[i])))
    
    # Travel constraints:
    # For the first active position: travel from Sunset (0) to the meeting's location
    for j in range(n_positions):
        if j == 0:
            for i_val in range(n_meetings):
                cond = And(active[j], order[j] == i_val)
                loc_i = loc_map[i_val]
                travel_time = travel_times[0][loc_i]
                s.add(Implies(cond, start[i_val] >= travel_time))
        else:
            # Travel from the previous meeting to the current meeting
            for prev_val in range(n_meetings):
                for curr_val in range(n_meetings):
                    if prev_val != curr_val:
                        cond = And(active[j-1], active[j], order[j-1]==prev_val, order[j]==curr_val)
                        loc_prev = loc_map[prev_val]
                        loc_curr = loc_map[curr_val]
                        travel_time = travel_times[loc_prev][loc_curr]
                        s.add(Implies(cond, start[curr_val] >= end[prev_val] + travel_time))
    
    # Maximize the number of meetings done
    num_meetings = Sum([If(do_i, 1, 0) for do_i in do])
    opt = Optimize()
    opt.add(s.assertions())
    h = opt.maximize(num_meetings)
    
    res = opt.check()
    if res == sat:
        m = opt.model()
        total_meetings = m.eval(num_meetings)
        print(f"Maximum number of meetings: {total_meetings}")
        
        # Get the sequence of meetings that are done
        seq = []
        for j in range(n_positions):
            val = m.eval(order[j])
            if val.as_long() >= 0:
                seq.append(val.as_long())
        
        # Print the schedule in the order of the sequence
        print("\nSchedule:")
        for idx in seq:
            start_time_min = m.eval(start[idx]).as_long()
            end_time_min = m.eval(end[idx]).as_long()
            # Convert minutes to time string
            start_hour = 9 + start_time_min // 60
            start_min = start_time_min % 60
            end_hour = 9 + end_time_min // 60
            end_min = end_time_min % 60
            start_str = f"{start_hour}:{start_min:02d}"
            end_str = f"{end_hour}:{end_min:02d}"
            print(f"  - {meeting_names[idx]}: from {start_str} to {end_str}")
    else:
        print("No solution found.")

if __name__ == '__main__':
    main()