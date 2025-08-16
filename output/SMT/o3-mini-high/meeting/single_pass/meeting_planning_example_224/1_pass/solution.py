from z3 import Optimize, Int, sat
import json

# Helper function to convert minutes-since-midnight to HH:MM string format
def format_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour:02d}:{minute:02d}"

# Create an optimization solver
opt = Optimize()

# Define meeting time variables (in minutes after midnight)
Melissa_start = Int('Melissa_start')
Melissa_end   = Int('Melissa_end')
Emily_start   = Int('Emily_start')
Emily_end     = Int('Emily_end')
Nancy_start   = Int('Nancy_start')
Nancy_end     = Int('Nancy_end')

# -------------------------------------------------------------------
# Constants (all times in minutes after midnight)
# Arrival at Fisherman's Wharf is at 9:00AM  -> 9*60 = 540 minutes.
# Friend availability windows:
#   Melissa is at Golden Gate Park from 08:30 (510) to 20:00 (1200) minutes.
#   Emily is at Richmond District from 16:45 (1005) to 22:00 (1320) minutes.
#   Nancy is at Presidio from 19:45 (1185) to 22:00 (1320) minutes.
# Travel times (in minutes):
#   Fisherman's Wharf -> Golden Gate Park: 25
#   Golden Gate Park -> Richmond District: 7
#   Richmond District -> Presidio: 7
# -------------------------------------------------------------------

# Constraint for meeting Melissa at Golden Gate Park:
# You must travel from Fisherman's Wharf to Golden Gate Park: 540 + 25 = 565 is the earliest arrival.
opt.add(Melissa_start >= 565)      # Cannot start before arriving at Golden Gate Park
opt.add(Melissa_start >= 510)      # Friend's availability start (redundant due to 565 > 510)
opt.add(Melissa_end <= 1200)       # Must finish before 20:00
opt.add(Melissa_end - Melissa_start >= 15)  # Minimum meeting duration 15 minutes

# Constraint for meeting Emily at Richmond District:
# You travel from Golden Gate Park to Richmond District in 7 minutes.
opt.add(Emily_start >= Melissa_end + 7)
# Emily is available from 16:45 (1005) to 22:00 (1320)
opt.add(Emily_start >= 1005)
opt.add(Emily_end <= 1320)
opt.add(Emily_end - Emily_start >= 120)  # Minimum meeting duration 120 minutes

# Constraint for meeting Nancy at Presidio:
# You travel from Richmond District to Presidio in 7 minutes.
opt.add(Nancy_start >= Emily_end + 7)
# Nancy is available from 19:45 (1185) to 22:00 (1320)
opt.add(Nancy_start >= 1185)
opt.add(Nancy_end <= 1320)
opt.add(Nancy_end - Nancy_start >= 105)  # Minimum meeting duration 105 minutes

# Enforce the meeting order
opt.add(Melissa_end <= Emily_start)
opt.add(Emily_end <= Nancy_start)

# Optional objective: minimize the completion time (end of Nancy meeting)
opt.minimize(Nancy_end)

# Check for a solution
if opt.check() == sat:
    m = opt.model()
    melissa_start_val = m[Melissa_start].as_long()
    melissa_end_val   = m[Melissa_end].as_long()
    emily_start_val   = m[Emily_start].as_long()
    emily_end_val     = m[Emily_end].as_long()
    nancy_start_val   = m[Nancy_start].as_long()
    nancy_end_val     = m[Nancy_end].as_long()
    
    itinerary = [
        {
            "action": "meet",
            "person": "Melissa",
            "start_time": format_time(melissa_start_val),
            "end_time": format_time(melissa_end_val)
        },
        {
            "action": "meet",
            "person": "Emily",
            "start_time": format_time(emily_start_val),
            "end_time": format_time(emily_end_val)
        },
        {
            "action": "meet",
            "person": "Nancy",
            "start_time": format_time(nancy_start_val),
            "end_time": format_time(nancy_end_val)
        }
    ]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=4))
else:
    print("No solution found.")