from z3 import *
import json

def minutes_to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Create an Optimize object and add our constraints.
opt = Optimize()

# Define time variables in minutes from midnight.
# For Carol’s meeting at Marina District.
c_start = Int('c_start')  # Carol meeting start time
c_end   = Int('c_end')    # Carol meeting end time

# For Jessica’s meeting at Pacific Heights.
j_start = Int('j_start')  # Jessica meeting start time
j_end   = Int('j_end')    # Jessica meeting end time

# The following are fixed travel durations (in minutes):
# Richmond -> Marina: 9 minutes.
# Marina -> Pacific Heights: 7 minutes.

# You arrive at Richmond District at 9:00 (540 minutes).
# Therefore, if you go directly to Marina, you’d arrive by 540+9 = 549.
# But Carol is only available from 11:30 (690 minutes). So we force:
opt.add(c_start >= 690)         # Carol available from 11:30
opt.add(c_end <= 15 * 60)         # Carol must be met before 15:00 (900 minutes)
opt.add(c_end - c_start >= 60)    # Minimum meeting duration with Carol is 60 minutes

opt.add(j_start >= 15 * 60 + 30)  # Jessica available from 15:30 (930 minutes)
opt.add(j_end <= 16 * 60 + 45)    # Jessica must be met by 16:45 (1005 minutes)
opt.add(j_end - j_start >= 45)    # Minimum meeting duration with Jessica is 45 minutes

# Travel constraints:
# From Richmond to Marina: Must leave after arriving at 9:00 and traveling 9 minutes.
opt.add(c_start >= 540 + 9)

# After finishing with Carol at Marina, you need to travel to Pacific Heights.
# This travel takes 7 minutes. Hence, Jessica’s meeting cannot start until
# at least c_end + 7 minutes.
opt.add(j_start >= c_end + 7)

# (Optional) To “optimize” the schedule, we can try to minimize idle waiting time.
# Idle before meeting Carol: (c_start - (arrival time at Marina))
idle_carol = c_start - (540 + 9)
# Idle after Carol meeting before Jessica meeting: (j_start - (c_end + 7))
idle_jessica = j_start - (c_end + 7)
opt.minimize(idle_carol + idle_jessica)

if opt.check() == sat:
    m = opt.model()
    # Extract the meeting times from the model.
    c_start_val = m[c_start].as_long()  # Carol meeting start time
    c_end_val   = m[c_end].as_long()    # Carol meeting end time
    j_start_val = m[j_start].as_long()  # Jessica meeting start time
    j_end_val   = m[j_end].as_long()    # Jessica meeting end time

    # Build the itinerary with the proper time string formatting.
    itinerary = [
        {
            "action": "meet",
            "person": "Carol",
            "start_time": minutes_to_time_str(c_start_val),
            "end_time": minutes_to_time_str(c_end_val)
        },
        {
            "action": "meet",
            "person": "Jessica",
            "start_time": minutes_to_time_str(j_start_val),
            "end_time": minutes_to_time_str(j_end_val)
        }
    ]
    
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))
else:
    print("No solution found.")