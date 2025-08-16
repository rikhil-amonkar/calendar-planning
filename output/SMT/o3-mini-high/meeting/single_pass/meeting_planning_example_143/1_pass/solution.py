from z3 import Optimize, Int, sat

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

opt = Optimize()

# --- Model Setup ---
# We represent times in minutes after midnight.
# 9:00AM   = 9*60 = 540
# 13:00    = 780
# 17:45    = 17*60+45 = 1065
# 18:45    = 18*60+45 = 1125
# 20:15    = 20*60+15 = 1215

# Travel durations (in minutes):
# North Beach --> Embarcadero          = 6
# Embarcadero  --> Pacific Heights     = 11
# (Other travel times are not needed because the meeting order is fixed.)

# Decision variables:
# Mark meeting at Embarcadero
M_s = Int("M_s")  # Mark meeting start time (minutes after midnight)
M_e = Int("M_e")  # Mark meeting end time

# Karen meeting at Pacific Heights
K_s = Int("K_s")  # Karen meeting start time
K_e = Int("K_e")  # Karen meeting end time

# --- Add Constraints ---

# We start the day at North Beach at 09:00.
# To reach Embarcadero for Mark's meeting, we add the travel time:
opt.add(M_s >= 540 + 6)  # i.e. M_s >= 546; but Mark’s window forces M_s >= 780 anyway.

# Mark is available at Embarcadero from 13:00 to 17:45.
opt.add(M_s >= 780)     # Meeting with Mark cannot start before 13:00.
opt.add(M_e <= 1065)    # And must finish by 17:45.
# You want to meet Mark for at least 120 minutes.
# For a “lean” schedule (so as not to waste extra time) we set exactly 120 minutes.
opt.add(M_e - M_s == 120)

# Karen is available at Pacific Heights from 18:45 to 20:15.
# Since the window lasts exactly 90 minutes, we fix her meeting interval.
opt.add(K_s == 1125)  # 18:45
opt.add(K_e == 1215)  # 20:15
# (The constraint "K_e - K_s >= 90" would force these values anyway.)

# After meeting Mark at Embarcadero, you need to travel to Pacific Heights.
# The travel time from Embarcadero to Pacific Heights is 11 minutes.
# Therefore, you must finish Mark's meeting early enough that when you add the travel time,
# you arrive by Karen's available start.
opt.add(K_s >= M_e + 11)

# --- Optimization Objective ---
# Although any valid solution meets the minimum requirements, a “good” schedule minimizes waiting time.
# Since Karen's meeting starts at 18:45, maximizing M_e (Mark's end time) reduces the idle gap.
opt.maximize(M_e)

# --- Solve and Print the Itinerary ---
if opt.check() == sat:
    model = opt.model()
    mark_start = model[M_s].as_long()
    mark_end = model[M_e].as_long()
    karen_start = model[K_s].as_long()  # This is fixed to 1125.
    karen_end = model[K_e].as_long()      # This is fixed to 1215.
    
    itinerary = []
    itinerary.append({
        "action": "meet",
        "person": "Mark",
        "start_time": minutes_to_time(mark_start),
        "end_time": minutes_to_time(mark_end)
    })
    itinerary.append({
        "action": "meet",
        "person": "Karen",
        "start_time": minutes_to_time(karen_start),
        "end_time": minutes_to_time(karen_end)
    })
    
    # The output is a JSON-formatted dictionary as specified.
    print({"itinerary": itinerary})
else:
    print("No solution found")