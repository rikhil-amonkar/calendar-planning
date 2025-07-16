from z3 import *

# Create a solver instance
s = Solver()

# Define variables for the time you leave Sunset District and arrive at Golden Gate Park
leave_sunset = Int('leave_sunset')
arrive_golden_gate = Int('arrive_golden_gate')

# Define the time you meet Joshua
meet_start = Int('meet_start')
meet_end = Int('meet_end')

# Constraints:
# 1. You arrive at Sunset District at 9:00 AM (540 minutes since midnight)
s.add(leave_sunset >= 540)  # Can't leave before 9:00 AM

# 2. Travel time from Sunset to Golden Gate Park is 11 minutes
s.add(arrive_golden_gate == leave_sunset + 11)

# 3. Joshua is available from 8:45 PM (1245 minutes) to 9:45 PM (1305 minutes)
# You must meet him for at least 15 minutes within this window
s.add(meet_start >= 1245)  # Meeting starts no earlier than 8:45 PM
s.add(meet_end <= 1305)    # Meeting ends no later than 9:45 PM
s.add(meet_end == meet_start + 15)  # Meeting lasts 15 minutes

# 4. You must arrive at Golden Gate Park before or at the meeting start time
s.add(arrive_golden_gate <= meet_start)

# Check if the constraints are satisfiable
if s.check() == sat:
    m = s.model()
    print("Solution found:")
    print(f"Leave Sunset District at: {m[leave_sunset].as_long()} minutes ({(m[leave_sunset].as_long() // 60)}:{(m[leave_sunset].as_long() % 60):02d} AM/PM)")
    print(f"Arrive at Golden Gate Park at: {m[arrive_golden_gate].as_long()} minutes ({(m[arrive_golden_gate].as_long() // 60)}:{(m[arrive_golden_gate].as_long() % 60):02d} AM/PM)")
    print(f"Meet Joshua from: {m[meet_start].as_long()} minutes ({(m[meet_start].as_long() // 60)}:{(m[meet_start].as_long() % 60):02d} AM/PM) to {m[meet_end].as_long()} minutes ({(m[meet_end].as_long() // 60)}:{(m[meet_end].as_long() % 60):02d} AM/PM)")
else:
    print("No possible schedule to meet Joshua under the given constraints.")