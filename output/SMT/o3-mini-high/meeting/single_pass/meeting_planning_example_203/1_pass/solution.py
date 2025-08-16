from z3 import Int, Optimize, sat
import json

# Time conversion helper: minutes since 9:00 to HH:MM (24-hour format)
def minutes_to_time(mins):
    # 9:00 is the base. So add 9 hours.
    hours = 9 + mins // 60
    minutes = mins % 60
    return f"{hours:02d}:{minutes:02d}"

# Create an Optimize object to possibly minimize waiting time 
opt = Optimize()

# Define variables (in minutes after 9:00)
# Meeting with Timothy at Pacific Heights
T_start = Int("T_start")  # start time of Timothy meeting
T_end   = Int("T_end")    # end time of Timothy meeting

# Meeting with David at Fisherman's Wharf
D_start = Int("D_start")
D_end   = Int("D_end")

# Meeting with Robert at Mission District
R_start = Int("R_start")
R_end   = Int("R_end")

# Travel times in minutes:
# from Financial District to Pacific Heights = 13
# from Pacific Heights to Fisherman's Wharf = 13
# from Fisherman's Wharf to Mission District = 22
transit_FP = 13  # Financial District -> Pacific Heights
transit_PF = 13  # Pacific Heights -> Fisherman's Wharf
transit_FM = 22  # Fisherman's Wharf -> Mission District

# Available time windows (in minutes after 9:00):
# Timothy at Pacific Heights: 9:00 (0) to 15:30 (6.5h = 390)
# David at Fisherman's Wharf: 10:45 (105) to 15:30 (390)
# Robert at Mission District: 12:15 (195) to 19:45 (645)
T_avail_start, T_avail_end = 0, 390
D_avail_start, D_avail_end = 105, 390
R_avail_start, R_avail_end = 195, 645

# Minimum meeting durations:
T_min_dur = 75
D_min_dur = 15
R_min_dur = 90

# -----------------------------------------------------------------
# Add constraints
# 1. Meeting with Timothy:
# Must arrive at Pacific Heights from Financial District: travel takes 13 minutes.
opt.add(T_start >= transit_FP)  # can start no earlier than 09:13
opt.add(T_start >= T_avail_start)
opt.add(T_end <= T_avail_end)
opt.add(T_end - T_start >= T_min_dur)

# 2. Meeting with David:
opt.add(D_start >= D_avail_start)
opt.add(D_end <= D_avail_end)
opt.add(D_end - D_start >= D_min_dur)
# Must travel from Pacific Heights (Timothy meeting) to Fisherman's Wharf:
opt.add(D_start >= T_end + transit_PF)

# 3. Meeting with Robert:
opt.add(R_start >= R_avail_start)
opt.add(R_end <= R_avail_end)
opt.add(R_end - R_start >= R_min_dur)
# Must travel from Fisherman's Wharf (David meeting) to Mission District:
opt.add(R_start >= D_end + transit_FM)

# Optional: Minimize total waiting time (unused time between travel and meeting start)
# Waiting time components:
# Waiting before starting Timothy meeting after arriving at Pacific Heights:
wait_T = T_start - transit_FP
# Waiting before starting David meeting after finishing Timothy meeting and traveling:
wait_D = D_start - (T_end + transit_PF)
# Waiting before starting Robert meeting after finishing David meeting and traveling:
wait_R = R_start - (D_end + transit_FM)
total_wait = wait_T + wait_D + wait_R
opt.minimize(total_wait)

# Check for a solution
if opt.check() == sat:
    model = opt.model()
    
    # Get the solution (minutes since 9:00)
    T_start_val = model[T_start].as_long()
    T_end_val   = model[T_end].as_long()
    D_start_val = model[D_start].as_long()
    D_end_val   = model[D_end].as_long()
    R_start_val = model[R_start].as_long()
    R_end_val   = model[R_end].as_long()
    
    # Build itinerary using the time conversion
    itinerary = [
        {"action": "meet", "person": "Timothy", 
         "start_time": minutes_to_time(T_start_val), "end_time": minutes_to_time(T_end_val)},
        {"action": "meet", "person": "David", 
         "start_time": minutes_to_time(D_start_val), "end_time": minutes_to_time(D_end_val)},
        {"action": "meet", "person": "Robert", 
         "start_time": minutes_to_time(R_start_val), "end_time": minutes_to_time(R_end_val)}
    ]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    print("No solution found.")