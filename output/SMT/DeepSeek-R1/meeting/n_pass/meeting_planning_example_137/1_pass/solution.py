from z3 import *

def min_to_time_str(mins):
    total = mins
    h = 9 + total // 60
    m = total % 60
    if h < 12:
        return f"{h}:{m:02d} AM"
    elif h == 12:
        return f"12:{m:02d} PM"
    else:
        if h > 12:
            h -= 12
        return f"{h}:{m:02d} PM"

s = Solver()

# Define variables
go_to_ggp_first = Bool('go_to_ggp_first')
t0 = Int('t0')
meeting1_start = Int('meeting1_start')
meeting1_end = Int('meeting1_end')
meeting2_start = Int('meeting2_start')
meeting2_end = Int('meeting2_end')

s.add(t0 >= 0)

# First location arrival time
arr1 = If(go_to_ggp_first, t0 + 23, t0 + 5)
s.add(meeting1_start >= arr1)
s.add(meeting1_end == meeting1_start + If(go_to_ggp_first, 45, 90))

# Travel to second location
arr2 = meeting1_end + 23
s.add(meeting2_start >= arr2)
s.add(meeting2_end == meeting2_start + If(go_to_ggp_first, 90, 45))

# Assign to friends
b_start = If(go_to_ggp_first, meeting1_start, meeting2_start)
b_end = If(go_to_ggp_first, meeting1_end, meeting2_end)
k_start = If(go_to_ggp_first, meeting2_start, meeting1_start)
k_end = If(go_to_ggp_first, meeting2_end, meeting1_end)

# Constraints from availability
s.add(b_end <= 600)   # Barbara available until 7:00 PM (600 minutes after 9:00 AM)
s.add(k_start >= 180) # Kenneth available from 12:00 PM (180 minutes)
s.add(k_end <= 360)   # Kenneth available until 3:00 PM (360 minutes)

if s.check() == sat:
    m = s.model()
    t0_val = m.eval(t0).as_long()
    go_to_ggp_first_val = is_true(m.eval(go_to_ggp_first))
    meeting1_start_val = m.eval(meeting1_start).as_long()
    meeting1_end_val = m.eval(meeting1_end).as_long()
    meeting2_start_val = m.eval(meeting2_start).as_long()
    meeting2_end_val = m.eval(meeting2_end).as_long()

    # Print the schedule
    print("SOLUTION:")
    print("Start at Financial District at 9:00 AM.")
    if go_to_ggp_first_val:
        print(f"  Leave Financial District at {min_to_time_str(t0_val)}")
        print(f"  Travel to Golden Gate Park (23 minutes)")
        print(f"  Arrive at Golden Gate Park at {min_to_time_str(t0_val + 23)}")
        print(f"  Meet Barbara from {min_to_time_str(meeting1_start_val)} to {min_to_time_str(meeting1_end_val)}")
        print(f"  Travel to Chinatown (23 minutes)")
        print(f"  Arrive at Chinatown at {min_to_time_str(meeting1_end_val + 23)}")
        print(f"  Meet Kenneth from {min_to_time_str(meeting2_start_val)} to {min_to_time_str(meeting2_end_val)}")
    else:
        print(f"  Leave Financial District at {min_to_time_str(t0_val)}")
        print(f"  Travel to Chinatown (5 minutes)")
        print(f"  Arrive at Chinatown at {min_to_time_str(t0_val + 5)}")
        print(f"  Meet Kenneth from {min_to_time_str(meeting1_start_val)} to {min_to_time_str(meeting1_end_val)}")
        print(f"  Travel to Golden Gate Park (23 minutes)")
        print(f"  Arrive at Golden Gate Park at {min_to_time_str(meeting1_end_val + 23)}")
        print(f"  Meet Barbara from {min_to_time_str(meeting2_start_val)} to {min_to_time_str(meeting2_end_val)}")
else:
    print("No solution found.")