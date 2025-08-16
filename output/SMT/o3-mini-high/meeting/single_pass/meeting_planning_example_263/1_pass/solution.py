from z3 import *
import json

# A utility function to convert minutes (since midnight) to "HH:MM" string.
def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

# We use minutes-from-midnight as our time unit.
# 9:00 AM is 9*60 = 540.
# Available windows (in minutes):
#   • Karen is at Fisherman's Wharf between 8:45 (525) and 15:00 (900) and needs ≥ 30 min.
#   • Anthony is at Financial District between 9:15 (555) and 21:30 (1290) and needs ≥ 105 min.
#   • Betty is at Embarcadero between 19:45 (1185) and 21:45 (1305) and needs ≥ 15 min.
#
# Travel times are given as:
#   • Bayview → Fisherman's Wharf: 25 min
#   • Bayview → Financial District: 19 min
#   • Fisherman's Wharf → Financial District: 11 min
#   • Financial District → Embarcadero: 4 min
# (Other travel times are provided, but here we adopt an ordering that visits:
#   Bayview (start) → Fisherman's Wharf (meet Karen) → Financial District (meet Anthony) → Embarcadero (meet Betty))
#
# We allow waiting time to “delay” the morning meetings so that the last transit to Betty coincides
# as closely as possible with her window’s start. Our objective is to meet all friends (maximizing
# the count) and “optimize” the schedule by minimizing idle waiting time.

# Create an Optimize object
opt = Optimize()

# Define integer variables for the meeting start and end times (in minutes from midnight)
s_k = Int('s_k')  # Karen meeting start (at Fisherman's Wharf)
e_k = Int('e_k')  # Karen meeting end
s_a = Int('s_a')  # Anthony meeting start (at Financial District)
e_a = Int('e_a')  # Anthony meeting end
s_b = Int('s_b')  # Betty meeting start (at Embarcadero)
e_b = Int('e_b')  # Betty meeting end

# ----------------------------
# 1. Constraints for each meeting based on availability and minimum duration

# Karen:
# - Must be met between 525 and 900.
# - Meeting must last at least 30 minutes.
# - Also, from the starting location Bayview (arriving at 540) we need to travel
#   to Fisherman's Wharf (25 min). So s_k must be at least 540+25 = 565.
opt.add(s_k >= 540 + 25)   # s_k >= 565
opt.add(s_k >= 525)        # Karen's window start
opt.add(e_k <= 900)        # Karen's window end
opt.add(e_k - s_k >= 30)   # Minimum 30 minutes

# Anthony:
# - Must be met between 555 and 1290.
# - Meeting must last at least 105 minutes.
# - In our chosen order, we come to Anthony after Karen.
#   Traveling from Fisherman's Wharf to Financial District takes 11 min; thus:
opt.add(s_a >= e_k + 11)
opt.add(s_a >= 555)        # Anthony's window start
opt.add(e_a <= 1290)       # Anthony's window end
opt.add(e_a - s_a >= 105)  # Minimum 105 minutes

# Betty:
# - Must be met between 1185 and 1305.
# - Meeting must last at least 15 minutes.
# - We travel from Anthony (Financial District) to Embarcadero in 4 min; thus:
opt.add(s_b >= e_a + 4)
opt.add(s_b >= 1185)       # Betty's window start
opt.add(e_b <= 1305)       # Betty's window end
opt.add(e_b - s_b >= 15)   # Minimum 15 minutes

# ----------------------------
# 2. OPTIONAL: Optimize the schedule by “synchronizing” the morning meetings as late as possible,
# thereby reducing waiting time before Betty’s window.
#
# Define waiting intervals:
#   wait1: waiting between leaving Karen and starting Anthony = s_a - (e_k + 11)
#   wait2: if Anthony’s meeting finishes too early, you must wait at Embarcadero until 1185.
#          That is, waiting between finishing Anthony and starting Betty is:
#               max(0, 1185 - (e_a + 4)).
#
# We introduce auxiliary integer variables:
wait1 = Int('wait1')
wait2 = Int('wait2')
opt.add(wait1 == s_a - (e_k + 11))
opt.add(wait1 >= 0)  # by construction this is non-negative

# For wait2, note that s_b is forced to be at least 1185 and at least (e_a + 4).
# To encourage an early start for Betty, we “target” s_b = 1185.
# So we set wait2 = 1185 - (e_a + 4). (This value will be forced to be nonnegative by the constraints.)
opt.add(wait2 == 1185 - (e_a + 4))
opt.add(wait2 >= 0)

# Our objective is to minimize the total idle waiting time:
objective = wait1 + wait2
opt.minimize(objective)

# ----------------------------
# Check for a solution and extract the schedule.
if opt.check() == sat:
    m = opt.model()
    # Build the itinerary in chronological order:
    itinerary = []
    itinerary.append({
        "action": "meet",
        "person": "Karen",
        "start_time": minutes_to_time(m[s_k].as_long()),
        "end_time": minutes_to_time(m[e_k].as_long())
    })
    itinerary.append({
        "action": "meet",
        "person": "Anthony",
        "start_time": minutes_to_time(m[s_a].as_long()),
        "end_time": minutes_to_time(m[e_a].as_long())
    })
    itinerary.append({
        "action": "meet",
        "person": "Betty",
        "start_time": minutes_to_time(m[s_b].as_long()),
        "end_time": minutes_to_time(m[e_b].as_long())
    })
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    print("No solution found")