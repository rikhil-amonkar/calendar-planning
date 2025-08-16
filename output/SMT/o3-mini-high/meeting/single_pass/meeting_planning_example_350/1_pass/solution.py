import json
from z3 import *

def minutes_to_time_str(m):
    # Convert minutes since midnight to "HH:MM" 24-hour string.
    h = m // 60
    mi = m % 60
    return f"{h:02d}:{mi:02d}"

# Create a Z3 solver instance.
solver = Solver()

# Define meeting start and end times (in minutes since midnight) for each friend.
s_b = Int('s_b')  # Betty's meeting start time at Haight-Ashbury.
e_b = Int('e_b')  # Betty's meeting end time.

s_m = Int('s_m')  # Mary's meeting start time at Pacific Heights.
e_m = Int('e_m')  # Mary's meeting end time.

s_c = Int('s_c')  # Charles's meeting start time at Financial District.
e_c = Int('e_c')  # Charles's meeting end time.

s_l = Int('s_l')  # Lisa's meeting start time at Mission District.
e_l = Int('e_l')  # Lisa's meeting end time.

# Constants: convert times to minutes since midnight.
arrival_bayview = 9 * 60              # 9:00 AM => 540 minutes.

# Friend availability windows (in minutes):
# Betty is available from 07:15 to 17:15.
betty_avail_start = 7 * 60 + 15         # 435
betty_avail_end   = 17 * 60 + 15        # 1035

# Mary is available from 10:00 to 19:00.
mary_avail_start = 10 * 60              # 600
mary_avail_end   = 19 * 60              # 1140

# Charles is available from 11:15 to 15:00.
charles_avail_start = 11 * 60 + 15      # 675
charles_avail_end   = 15 * 60           # 900

# Lisa is available from 20:30 to 22:00.
lisa_avail_start = 20 * 60 + 30         # 1230
lisa_avail_end   = 22 * 60              # 1320

# Travel times between locations (in minutes):
# Bayview -> Haight-Ashbury: 19 minutes.
# Haight-Ashbury -> Pacific Heights: 12 minutes.
# Pacific Heights -> Financial District: 13 minutes.
# Financial District -> Mission District: 17 minutes.

# Add constraints for Betty at Haight-Ashbury.
# We start at Bayview at 9:00 (540) and must travel 19 minutes.
solver.add(s_b >= arrival_bayview + 19)
# Also, Betty is available from 7:15.
solver.add(s_b >= betty_avail_start)
# Meeting with Betty must finish by her availability end.
solver.add(e_b <= betty_avail_end)
# The meeting must last at least 90 minutes.
solver.add(e_b - s_b >= 90)

# Add constraints for Mary at Pacific Heights.
# Mary is available from 10:00.
solver.add(s_m >= mary_avail_start)
# Must allow travel from Betty (Haight-Ashbury) to Pacific Heights: 12 minutes.
solver.add(s_m >= e_b + 12)
# The meeting must end by 19:00.
solver.add(e_m <= mary_avail_end)
# The meeting must last at least 45 minutes.
solver.add(e_m - s_m >= 45)

# Add constraints for Charles at Financial District.
# Charles is available from 11:15.
solver.add(s_c >= charles_avail_start)
# Travel from Mary (Pacific Heights) to Financial District takes 13 minutes.
solver.add(s_c >= e_m + 13)
# The meeting must finish by 15:00.
solver.add(e_c <= charles_avail_end)
# The meeting must last at least 120 minutes.
solver.add(e_c - s_c >= 120)

# Add constraints for Lisa at Mission District.
# Lisa is available from 20:30.
solver.add(s_l >= lisa_avail_start)
# Travel from Charles (Financial District) to Mission District takes 17 minutes.
solver.add(s_l >= e_c + 17)
# The meeting must finish by 22:00.
solver.add(e_l <= lisa_avail_end)
# The meeting must last at least 75 minutes.
solver.add(e_l - s_l >= 75)

# Solve the scheduling constraints.
if solver.check() == sat:
    model = solver.model()
    
    itinerary = []
    itinerary.append({
        "action": "meet",
        "person": "Betty",
        "start_time": minutes_to_time_str(model[s_b].as_long()),
        "end_time": minutes_to_time_str(model[e_b].as_long())
    })
    itinerary.append({
        "action": "meet",
        "person": "Mary",
        "start_time": minutes_to_time_str(model[s_m].as_long()),
        "end_time": minutes_to_time_str(model[e_m].as_long())
    })
    itinerary.append({
        "action": "meet",
        "person": "Charles",
        "start_time": minutes_to_time_str(model[s_c].as_long()),
        "end_time": minutes_to_time_str(model[e_c].as_long())
    })
    itinerary.append({
        "action": "meet",
        "person": "Lisa",
        "start_time": minutes_to_time_str(model[s_l].as_long()),
        "end_time": minutes_to_time_str(model[e_l].as_long())
    })
    
    solution = {"itinerary": itinerary}
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")