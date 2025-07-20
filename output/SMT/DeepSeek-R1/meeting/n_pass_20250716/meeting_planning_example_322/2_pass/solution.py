from z3 import *

def main():
    # Travel time matrix: [from][to]
    # Index: 0:Sunset, 1:Chinatown, 2:Fisherman's Wharf, 3:Presidio, 4:Russian Hill
    travel = [
        [0, 30, 29, 16, 24],
        [29, 0, 8, 19, 7],
        [27, 12, 0, 17, 7],
        [15, 21, 19, 0, 14],
        [23, 9, 7, 14, 0]
    ]
    
    # Friend info: (window_start, window_end, min_time) in minutes from 9:00 AM (0)
    friend_info = {
        1: (-45, 300, 15),   # Michelle (Chinatown): 8:15AM to 2:00PM, min 15 min
        2: (0, 285, 30),     # Robert (Fisherman's Wharf): 9:00AM to 1:45PM, min 30 min
        3: (90, 585, 30),    # George (Presidio): 10:30AM to 6:45PM, min 30 min
        4: (570, 705, 105)   # William (Russian Hill): 6:30PM to 8:45PM, min 105 min
    }
    
    # Slot variables: each slot can be 0 (skip) or 1-4 (friend index)
    slots = [Int(f'slot{i}') for i in range(4)]
    s = [Real(f's{i}') for i in range(4)]  # Start times for each slot
    d = [Real(f'd{i}') for i in range(4)]  # Departure times for each slot
    
    # Create an optimizer
    opt = Optimize()
    
    # Constraints for slot values: 0 to 4
    for i in range(4):
        opt.add(slots[i] >= 0, slots[i] <= 4)
    
    # Distinct non-zero slots
    for i in range(4):
        for j in range(i+1, 4):
            opt.add(Or(slots[i] == 0, slots[j] == 0, slots[i] != slots[j]))
    
    # Initialize variables for the timeline
    prev_dep = Real('start')  # Start at time 0 (9:00 AM)
    opt.add(prev_dep == 0.0)
    prev_loc = Int('start_loc')
    opt.add(prev_loc == 0)     # Start at Sunset (location 0)
    total_meetings = Int('total_meetings')
    opt.add(total_meetings == 0)  # Initialize to 0
    
    # Process each slot
    for i in range(4):
        k = slots[i]
        # Calculate travel time based on previous location and current slot
        base = RealVal(0)
        for loc in range(5):
            for friend_idx in range(1,5):
                base = If(And(prev_loc == loc, k == friend_idx), travel[loc][friend_idx], base)
        travel_time_i = If(k == 0, 0, base)
        
        arrival_i = prev_dep + travel_time_i
        
        # If meeting, set constraints; else, skip
        meeting_occur = (k != 0)
        # Start time must be at least arrival time and within friend's window
        opt.add(If(meeting_occur, s[i] >= arrival_i, True))
        opt.add(If(meeting_occur, s[i] >= friend_info[k][0], True))
        opt.add(If(meeting_occur, s[i] <= friend_info[k][1] - friend_info[k][2], True))
        # Departure time is start time plus meeting duration
        opt.add(If(meeting_occur, d[i] == s[i] + friend_info[k][2], d[i] == prev_dep))
        # Update location if meeting occurred
        next_loc = If(meeting_occur, k, prev_loc)
        # Update total meetings
        total_meetings = If(meeting_occur, total_meetings + 1, total_meetings)
        
        # Prepare for next slot
        prev_dep = d[i]
        prev_loc = next_loc
    
    # Maximize the number of meetings
    opt.maximize(total_meetings)
    
    # Check for a solution
    if opt.check() == sat:
        model = opt.model()
        total_met = model.eval(total_meetings)
        print(f"Total friends met: {total_met}")
        
        # Print the schedule
        prev_dep_val = 0.0
        prev_loc_val = 0
        for i in range(4):
            k_val = model.eval(slots[i]).as_long()
            s_val = model.eval(s[i])
            d_val = model.eval(d[i])
            if k_val != 0:
                # Calculate travel time
                travel_time_val = travel[prev_loc_val][k_val]
                arrival_val = prev_dep_val + travel_time_val
                start_minutes = s_val.as_fraction().numerator / s_val.as_fraction().denominator
                end_minutes = d_val.as_fraction().numerator / d_val.as_fraction().denominator
                # Convert minutes to time (from 9:00 AM)
                start_time = (540 + start_minutes) % (24 * 60)
                end_time = (540 + end_minutes) % (24 * 60)
                start_hour = int(start_time // 60)
                start_minute = int(start_time % 60)
                end_hour = int(end_time // 60)
                end_minute = int(end_time % 60)
                friend_name = {
                    1: "Michelle (Chinatown)",
                    2: "Robert (Fisherman's Wharf)",
                    3: "George (Presidio)",
                    4: "William (Russian Hill)"
                }[k_val]
                print(f"Slot {i}: Meet {friend_name}")
                print(f"  Travel from {prev_loc_val} to {k_val}: {travel_time_val} minutes")
                print(f"  Arrival: {start_hour:02d}:{start_minute:02d}, Meeting: {start_hour:02d}:{start_minute:02d} to {end_hour:02d}:{end_minute:02d}")
                prev_dep_val = end_minutes
                prev_loc_val = k_val
            else:
                print(f"Slot {i}: Skip")
                # No travel, location remains
                prev_dep_val = d_val.as_fraction().numerator / d_val.as_fraction().denominator
    else:
        print("No solution found")

if __name__ == "__main__":
    main()