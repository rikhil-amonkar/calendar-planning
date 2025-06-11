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
    avail_start = {
        1: 13*60 + 45,  # 1:45 PM
        2: 10*60 + 15,  # 10:15 AM
        3: 20*60 + 0,   # 8:00 PM
        4: 7*60 + 45    # 7:45 AM
    }
    avail_end = {
        1: 20*60 + 15,  # 8:15 PM
        2: 15*60 + 15,  # 3:15 PM
        3: 20*60 + 45,  # 8:45 PM
        4: 16*60 + 45   # 4:45 PM
    }
    min_dur = {
        1: 60,
        2: 30,
        3: 30,
        4: 30
    }
    
    # Initial location (Bayview) and time (9:00 AM = 540 minutes)
    current_loc = 0
    current_time = 540
    
    # Constraints for slot0
    cond0 = (slot0 != 0)
    s.add(Implies(cond0, start0 >= current_time + get_travel_time(current_loc, slot0)))
    s.add(Implies(cond0, start0 >= avail_start[slot0]))
    s.add(Implies(cond0, start0 + min_dur[slot0] <= avail_end[slot0]))
    next_loc0 = If(cond0, slot0, current_loc)
    next_time0 = If(cond0, start0 + min_dur[slot0], current_time)
    
    # Constraints for slot1
    cond1 = (slot1 != 0)
    s.add(Implies(cond1, start1 >= next_time0 + get_travel_time(next_loc0, slot1)))
    s.add(Implies(cond1, start1 >= avail_start[slot1]))
    s.add(Implies(cond1, start1 + min_dur[slot1] <= avail_end[slot1]))
    next_loc1 = If(cond1, slot1, next_loc0)
    next_time1 = If(cond1, start1 + min_dur[slot1], next_time0)
    
    # Constraints for slot2
    cond2 = (slot2 != 0)
    s.add(Implies(cond2, start2 >= next_time1 + get_travel_time(next_loc1, slot2)))
    s.add(Implies(cond2, start2 >= avail_start[slot2]))
    s.add(Implies(cond2, start2 + min_dur[slot2] <= avail_end[slot2]))
    next_loc2 = If(cond2, slot2, next_loc1)
    next_time2 = If(cond2, start2 + min_dur[slot2], next_time1)
    
    # Constraints for slot3
    cond3 = (slot3 != 0)
    s.add(Implies(cond3, start3 >= next_time2 + get_travel_time(next_loc2, slot3)))
    s.add(Implies(cond3, start3 >= avail_start[slot3]))
    s.add(Implies(cond3, start3 + min_dur[slot3] <= avail_end[slot3]))
    
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
        
        def min_to_time(mins):
            h = mins // 60
            m = mins % 60
            return f"{h:02d}:{m:02d}"
        
        current_loc = 0
        current_time = 540
        print(f"Start at Bayview at 09:00")
        slots = [slot0, slot1, slot2, slot3]
        starts = [start0, start1, start2, start3]
        for idx, slot_var in enumerate(slots):
            slot_val = m[slot_var].as_long()
            if slot_val == 0:
                continue
            start_val = m[starts[idx]].as_long()
            travel_t = travel_py[current_loc][slot_val]
            end_time = start_val + min_dur[slot_val]
            print(f"Travel from {loc_names[current_loc]} to {loc_names[slot_val]} ({travel_t} minutes)")
            print(f"Meet {loc_names[slot_val]} from {min_to_time(start_val)} to {min_to_time(end_time)}")
            current_loc = slot_val
            current_time = end_time
        total_met = m[total_meetings].as_long()
        print(f"Total friends met: {total_met}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()