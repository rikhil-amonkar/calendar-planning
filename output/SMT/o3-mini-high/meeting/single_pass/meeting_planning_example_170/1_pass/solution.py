from z3 import Optimize, Int, sat
import json

# Create the optimization solver
opt = Optimize()

# Define time variables (in minutes after midnight)
# 9:00 AM is 9*60 = 540 minutes.
E_start = Int("E_start")  # Emily meeting start time
E_end = Int("E_end")      # Emily meeting end time
M_start = Int("M_start")  # Margaret meeting start time
M_end = Int("M_end")      # Margaret meeting end time
D_NB = Int("D_NB")        # Departure time from North Beach

# Constants (in minutes after midnight)
NB_arrival = 9 * 60          # 09:00 -> 540 minutes
E_avail_start = 16 * 60      # 16:00 -> 960 minutes
E_avail_end = 17 * 60 + 15   # 17:15 -> 1035 minutes
M_avail_start = 19 * 60      # 19:00 -> 1140 minutes
M_avail_end = 21 * 60        # 21:00 -> 1260 minutes

# Travel times in minutes between locations (given)
NB_to_US = 7     # North Beach -> Union Square
US_to_RH = 13    # Union Square -> Russian Hill
# (Other travel times are provided but are not needed for these meetings.)

# Constraints for Emily's meeting at Union Square
opt.add(E_start >= E_avail_start)          # Cannot start before 16:00
opt.add(E_end <= E_avail_end)              # Must end by 17:15
opt.add(E_end - E_start >= 45)             # Meet Emily for at least 45 minutes

# Constraints for Margaret's meeting at Russian Hill
opt.add(M_start >= M_avail_start)          # Cannot start before 19:00
opt.add(M_end <= M_avail_end)              # Must end by 21:00
opt.add(M_end - M_start >= 120)            # Meet Margaret for at least 120 minutes

# Travel constraints:
# From North Beach (arrival at 09:00) to Union Square for Emily:
opt.add(D_NB >= NB_arrival)                # Can depart only after arriving at North Beach
opt.add(D_NB + NB_to_US <= E_start)          # Arrive at Union Square in time for Emily

# From Union Square (after Emily's meeting) to Russian Hill for Margaret:
opt.add(E_end + US_to_RH <= M_start)         # Enough travel time between meetings

# Objective: maximize the total meeting durations
# (This pushes the solution to use as much of each friend's available window as possible.)
total_meeting_time = (E_end - E_start) + (M_end - M_start)
opt.maximize(total_meeting_time)

# Solve the optimization problem
if opt.check() == sat:
    model = opt.model()
    # Extract model values
    e_start_val = model[E_start].as_long()
    e_end_val = model[E_end].as_long()
    m_start_val = model[M_start].as_long()
    m_end_val = model[M_end].as_long()
    
    # Function to convert minutes to HH:MM (24-hour) format
    def format_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"
    
    itinerary = [
        {
            "action": "meet",
            "person": "Emily",
            "start_time": format_time(e_start_val),
            "end_time": format_time(e_end_val)
        },
        {
            "action": "meet",
            "person": "Margaret",
            "start_time": format_time(m_start_val),
            "end_time": format_time(m_end_val)
        }
    ]
    
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=4))
else:
    print("No solution found.")