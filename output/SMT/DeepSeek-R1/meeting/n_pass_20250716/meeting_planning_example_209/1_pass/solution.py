from z3 import *

def main():
    # Meeting indices: 0 = Melissa, 1 = Anthony, 2 = Rebecca
    meet_names = ['Melissa', 'Anthony', 'Rebecca']
    # Map meeting index to location index: Sunset=0, North Beach=1, Chinatown=2, Russian Hill=3
    loc_map = [1, 2, 3]  # Melissa at North Beach (1), Anthony at Chinatown (2), Rebecca at Russian Hill (3)
    
    # Availability and duration constraints (in minutes from 9:00 AM)
    start_avail = [29, 255, 630]    # Earliest start times
    end_avail = [270, 330, 735]     # Latest end times
    min_dur = [105, 60, 105]        # Minimum durations
    
    # Travel time matrix: [from][to] 
    # Indices: 0=Sunset, 1=North Beach, 2=Chinatown, 3=Russian Hill
    travel = [
        [0, 29, 30, 24],   # From Sunset
        [27, 0, 6, 4],     # From North Beach
        [29, 3, 0, 7],     # From Chinatown
        [23, 5, 9, 0]      # From Russian Hill
    ]
    
    # Create solver
    s = Optimize()
    
    # Decision variables
    meet_vars = [Bool(f'meet_{i}') for i in range(3)]  # Whether to meet each friend
    slots = [Int(f'slot_{i}') for i in range(3)]       # Meeting in each slot (-1 for empty)
    start_times = [Real(f'start_{i}') for i in range(3)] # Start time for each slot
    
    # Each slot must be -1 or a valid meeting index (0,1,2)
    for i in range(3):
        s.add(Or(slots[i] == -1, slots[i] == 0, slots[i] == 1, slots[i] == 2))
    
    # If a meeting is chosen, it must appear in exactly one slot
    for j in range(3):
        s.add(meet_vars[j] == Or([slots[i] == j for i in range(3)]))
    
    # Non-chosen meetings must not appear in any slot
    for j in range(3):
        for i in range(3):
            s.add(Implies(Not(meet_vars[j]), slots[i] != j))
    
    # Ensure no duplicate meetings in slots
    for i in range(3):
        for j in range(i+1, 3):
            s.add(Implies(And(slots[i] >= 0, slots[j] >= 0), slots[i] != slots[j]))
    
    # If a slot is empty, subsequent slots must also be empty
    for i in range(2):
        s.add(Implies(slots[i] == -1, slots[i+1] == -1))
    
    # Constraints for slot 0
    slot0_cond = []
    for idx in range(3):
        loc_idx = loc_map[idx]
        cond = (slots[0] == idx)
        slot0_cond.append(Implies(cond, And(
            start_times[0] >= travel[0][loc_idx],
            start_times[0] >= start_avail[idx],
            start_times[0] + min_dur[idx] <= end_avail[idx]
        )))
    s.add(Implies(slots[0] != -1, And(slot0_cond)))
    
    # Constraints for slot 1
    slot1_cond = []
    for prev_idx in range(3):
        for curr_idx in range(3):
            prev_loc = loc_map[prev_idx]
            curr_loc = loc_map[curr_idx]
            cond = And(slots[0] == prev_idx, slots[1] == curr_idx)
            slot1_cond.append(Implies(cond, 
                start_times[1] >= start_times[0] + min_dur[prev_idx] + travel[prev_loc][curr_loc]
            ))
    slot1_cond2 = []
    for idx in range(3):
        cond = (slots[1] == idx)
        slot1_cond2.append(Implies(cond, And(
            start_times[1] >= start_avail[idx],
            start_times[1] + min_dur[idx] <= end_avail[idx]
        )))
    s.add(Implies(slots[1] != -1, And(slot1_cond + slot1_cond2)))
    
    # Constraints for slot 2
    slot2_cond = []
    for prev_idx in range(3):
        for curr_idx in range(3):
            prev_loc = loc_map[prev_idx]
            curr_loc = loc_map[curr_idx]
            cond = And(slots[1] == prev_idx, slots[2] == curr_idx)
            slot2_cond.append(Implies(cond, 
                start_times[2] >= start_times[1] + min_dur[prev_idx] + travel[prev_loc][curr_loc]
            ))
    slot2_cond2 = []
    for idx in range(3):
        cond = (slots[2] == idx)
        slot2_cond2.append(Implies(cond, And(
            start_times[2] >= start_avail[idx],
            start_times[2] + min_dur[idx] <= end_avail[idx]
        )))
    s.add(Implies(slots[2] != -1, And(slot2_cond + slot2_cond2)))
    
    # Start times must be non-negative
    for i in range(3):
        s.add(start_times[i] >= 0)
    
    # Maximize the number of meetings
    total_meetings = Sum([If(meet_vars[i], 1, 0) for i in range(3)])
    s.maximize(total_meetings)
    
    # Check and output solution
    if s.check() == sat:
        m = s.model()
        print("Schedule:")
        # Print meetings in slot order
        for slot_idx in range(3):
            slot_val = m[slots[slot_idx]]
            if slot_val.as_long() != -1:
                start_val = m[start_times[slot_idx]]
                start_min = start_val.as_decimal(10)
                # Convert minutes back to time
                total_minutes = int(float(str(start_val)))
                hours = 9 + total_minutes // 60
                minutes = total_minutes % 60
                end_time = total_minutes + min_dur[slot_val.as_long()]
                end_hours = 9 + end_time // 60
                end_minutes = end_time % 60
                print(f"Slot {slot_idx}: Meet {meet_names[slot_val.as_long()]} from {hours}:{minutes:02d} to {end_hours}:{end_minutes:02d}")
        # Print which friends are met
        for i in range(3):
            if m.evaluate(meet_vars[i]):
                print(f"Met {meet_names[i]}")
        print(f"Total meetings: {m.evaluate(total_meetings)}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()