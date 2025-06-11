from z3 import *

def main():
    s = Optimize()
    
    # Define slot variables: each can be 0 (no meeting) or 1-4 (friend's location)
    slot0 = Int('slot0')
    slot1 = Int('slot1')
    slot2 = Int('slot2')
    slot3 = Int('slot3')
    
    # Define start time variables for each slot
    start0 = Int('start0')
    start1 = Int('start1')
    start2 = Int('start2')
    start3 = Int('start3')
    
    # Each slot must be between 0 and 4
    s.add(And(slot0 >= 0, slot0 <= 4))
    s.add(And(slot1 >= 0, slot1 <= 4))
    s.add(And(slot2 >= 0, slot2 <= 4))
    s.add(And(slot3 >= 0, slot3 <= 4))
    
    # If a slot is 0, all subsequent must be 0
    s.add(Implies(slot0 == 0, slot1 == 0))
    s.add(Implies(slot1 == 0, slot2 == 0))
    s.add(Implies(slot2 == 0, slot3 == 0))
    
    # Each friend (1-4) can be met at most once
    friends = [1, 2, 3, 4]
    for f in friends:
        count_f = If(slot0 == f, 1, 0) + If(slot1 == f, 1, 0) + If(slot2 == f, 1, 0) + If(slot3 == f, 1, 0)
        s.add(count_f <= 1)
    
    # Travel time matrix (5x5: 0=Bayview, 1=North Beach, 2=Presidio, 3=Haight-Ashbury, 4=Union Square)
    travel_py = [
        [0, 21, 31, 19, 17],
        [22, 0, 17, 18, 7],
        [31, 18, 0, 15, 22],
        [18, 19, 15, 0, 17],
        [15, 10, 24, 18, 0]
    ]
    
    # Build Z3 array for travel times
    travel_array = Array('travel_array', IntSort(), ArraySort(IntSort(), IntSort()))
    for i in range(5):
        inner = Array(f'inner_{i}', IntSort(), IntSort())
        for j in range(5):
            inner = Store(inner, j, travel_py[i][j])
        travel_array = Store(travel_array, i, inner)
    
    def get_travel_time(from_loc, to_loc):
        return Select(Select(travel_array, from_loc), to_loc)
    
    # Friend availability and meeting durations (in minutes from midnight)
    # Create Z3 arrays for availability start, end, and min duration
    avail_start_arr = Array('avail_start_arr', IntSort(), IntSort())
    avail_end_arr = Array('avail_end_arr', IntSort(), IntSort())
    min_dur_arr = Array('min_dur_arr', IntSort(), IntSort())
    
    # Set values for locations 1 to 4
    locs = [1, 2, 3, 4]
    start_vals = [13*60 + 45, 10*60 + 15, 20*60 + 0, 7*60 + 45]  # 1: Barbara, 2: Margaret, 3: Kevin, 4: Kimberly
    end_vals = [20*60 + 15, 15*60 + 15, 20*60 + 45, 16*60 + 45]
    dur_vals = [60, 30, 30, 30]
    
    for loc, s_val, e_val, d_val in zip(locs, start_vals, end_vals, dur_vals):
        avail_start_arr = Store(avail_start_arr, loc, s_val)
        avail_end_arr = Store(avail_end_arr, loc, e_val)
        min_dur_arr = Store(min_dur_arr, loc, d_val)
    
    # Initial location (Bayview) and time (9:00 AM = 540 minutes)
    current_loc = 0
    current_time = 540
    
    # Constraints for slot0
    cond0 = (slot0 != 0)
    s.add(Implies(cond0, start0 >= current_time + get_travel_time(current_loc, slot0)))
    s.add(Implies(cond0, start0 >= Select(avail_start_arr, slot0)))
    s.add(Implies(cond0, start0 + Select(min_dur_arr, slot0) <= Select(avail_end_arr, slot0)))
    next_loc0 = If(cond0, slot0, current_loc)
    next_time0 = If(cond0, start0 + Select(min_dur_arr, slot0), current_time)
    
    # Constraints for slot1
    cond1 = (slot1 != 0)
    s.add(Implies(cond1, start1 >= next_time0 + get_travel_time(next_loc0, slot1)))
    s.add(Implies(cond1, start1 >= Select(avail_start_arr, slot1)))
    s.add(Implies(cond1, start1 + Select(min_dur_arr, slot1) <= Select(avail_end_arr, slot1)))
    next_loc1 = If(cond1, slot1, next_loc0)
    next_time1 = If(cond1, start1 + Select(min_dur_arr, slot1), next_time0)
    
    # Constraints for slot2
    cond2 = (slot2 != 0)
    s.add(Implies(cond2, start2 >= next_time1 + get_travel_time(next_loc1, slot2)))
    s.add(Implies(cond2, start2 >= Select(avail_start_arr, slot2)))
    s.add(Implies(cond2, start2 + Select(min_dur_arr, slot2) <= Select(avail_end_arr, slot2)))
    next_loc2 = If(cond2, slot2, next_loc1)
    next_time2 = If(cond2, start2 + Select(min_dur_arr, slot2), next_time1)
    
    # Constraints for slot3
    cond3 = (slot3 != 0)
    s.add(Implies(cond3, start3 >= next_time2 + get_travel_time(next_loc2, slot3)))
    s.add(Implies(cond3, start3 >= Select(avail_start_arr, slot3)))
    s.add(Implies(cond3, start3 + Select(min_dur_arr, slot3) <= Select(avail_end_arr, slot3)))
    
    # Objective: maximize the number of meetings (non-zero slots)
    total_meetings = If(slot0 != 0, 1, 0) + If(slot1 != 0, 1, 0) + If(slot2 != 0, 1, 0) + If(slot3 != 0, 1, 0)
    s.maximize(total_meetings)
    
    if s.check() == sat:
        m = s.model()
        print("SOLUTION:")
        loc_names = {
            0: "Bayview",
            1: "Barbara at North Beach",
            2: "Margaret at Presidio",
            3: "Kevin at Haight-Ashbury",
            4: "Kimberly at Union Square"
        }
        
        min_dur_dict = {1: 60, 2: 30, 3: 30, 4: 30}
        
        def min_to_time(mins):
            h = mins // 60
            m = mins % 60
            am_pm = "AM" if h < 12 else "PM"
            if h == 0:
                h = 12
            elif h > 12:
                h -= 12
            return f"{h}:{m:02d}{am_pm}"
        
        current_loc = 0
        current_time = 540
        print(f"Start at Bayview at 09:00AM")
        slots = [slot0, slot1, slot2, slot3]
        starts = [start0, start1, start2, start3]
        for idx, slot_var in enumerate(slots):
            slot_val = m[slot_var].as_long()
            if slot_val == 0:
                continue
            start_val = m[starts[idx]].as_long()
            travel_t = travel_py[current_loc][slot_val]
            end_time = start_val + min_dur_dict[slot_val]
            print(f"Travel from {loc_names[current_loc]} to {loc_names[slot_val]} ({travel_t} minutes)")
            print(f"Meet {loc_names[slot_val]} from {min_to_time(start_val)} to {min_to_time(end_time)}")
            current_loc = slot_val
            current_time = end_time
        total_met = sum(1 for slot_var in slots if m[slot_var].as_long() != 0)
        print(f"Total friends met: {total_met}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()