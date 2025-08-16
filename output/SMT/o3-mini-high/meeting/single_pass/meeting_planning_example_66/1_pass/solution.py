from z3 import Optimize, Int, sat
import json

# Constants (all times are in minutes after midnight)
arrival_nob_hill = 9 * 60           # 9:00 AM -> 540 minutes
robert_available_start = 11 * 60 + 15 # 11:15 AM -> 675 minutes
robert_available_end   = 17 * 60 + 45 # 17:45 -> 1065 minutes
travel_nh_to_presidio  = 17         # minutes from Nob Hill to Presidio
travel_pres_to_nh      = 18         # minutes from Presidio to Nob Hill

# Create an optimizer instance
opt = Optimize()

# Decision variables:
#  d: departure time from Nob Hill (in minutes after midnight)
#  r_start: meeting start time with Robert (arrival time at Presidio)
#  r_end: meeting end time with Robert
d = Int('d')
r_start = Int('r_start')
r_end = Int('r_end')

# Add constraints:
# 1. You arrive at Nob Hill at 9:00, so you cannot leave before 540 minutes.
opt.add(d >= arrival_nob_hill)

# 2. The travel from Nob Hill to Presidio takes 17 minutes.
#    Therefore, once you depart at time d, you’ll arrive at Presidio at time d + 17.
opt.add(r_start == d + travel_nh_to_presidio)

# 3. Robert is available at Presidio from 11:15 to 17:45.
opt.add(r_start >= robert_available_start)
opt.add(r_end <= robert_available_end)

# 4. You want to meet Robert for at least 120 minutes.
opt.add(r_end - r_start >= 120)

# Objective:
# Since you want to meet as many friends as possible during the day,
# you prefer to satisfy the minimum meeting duration with Robert so that you have the rest of the day free.
# Therefore, you want to schedule Robert's meeting as early and as short as possible.
h1 = opt.minimize(d)      # depart as early as you can (at or after 9:00)
h2 = opt.minimize(r_end)   # finish Robert's meeting as early as possible (while meeting the minimum 120 minutes)

# Check for a solution.
if opt.check() == sat:
    model = opt.model()
    d_val = model[d].as_long()          # departure time from Nob Hill
    r_start_val = model[r_start].as_long()  # meeting start time with Robert (arrival at Presidio)
    r_end_val = model[r_end].as_long()      # meeting end time with Robert

    # Utility function to convert minutes into HH:MM (24-hour) format.
    def minutes_to_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02}:{mins:02}"

    itinerary = [
        {
            "action": "meet",
            "person": "Robert",
            "start_time": minutes_to_time(r_start_val),
            "end_time": minutes_to_time(r_end_val)
        }
    ]
    
    # The final itinerary as a JSON-formatted dictionary.
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=4))
else:
    print("No solution found.")