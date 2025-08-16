from z3 import *
import json

# Times are measured in minutes from midnight.
# Constants:
# 9:00 AM = 540 minutes, 8:15 AM = 495, 11:30 AM = 690,
# 10:15 AM = 615, and 20:45 = 1245.
arrival_embarcadero = 540  # 9:00 AM

# Travel times in minutes:
t_E_to_F = 5      # Embarcadero -> Financial District
t_F_to_A = 17     # Financial District -> Alamo Square
# (Other travel times are given but are not used in this specific schedule.)

# Create Z3 integer variables representing meeting start and end times (in minutes)
S_start = Int('S_start')  # Start time of meeting with Stephanie at Financial District
S_end   = Int('S_end')    # End time of meeting with Stephanie at Financial District

J_start = Int('J_start')  # Start time of meeting with John at Alamo Square
J_end   = Int('J_end')    # End time of meeting with John at Alamo Square

# Create an optimizer and add the constraints.
opt = Optimize()

# Constraint: To meet Stephanie (available at Financial District from 8:15 to 11:30),
# you have to leave Embarcadero (arrival at 9:00) and travel 5 minutes.
opt.add(S_start >= arrival_embarcadero + t_E_to_F)  # S_start >= 540+5 = 545 minutes
opt.add(S_start >= 495)  # Stephanie is available from 8:15 (495) 
opt.add(S_end <= 690)    # and until 11:30 (690)
opt.add(S_end - S_start >= 90)  # Meet Stephanie for at least 90 minutes

# Constraint: To meet John (available at Alamo Square from 10:15 to 20:45)
# he must be met after traveling from the Financial District to Alamo Square.
opt.add(J_start >= 615)      # John is available from 10:15 (615)
opt.add(J_end <= 1245)       # and until 20:45 (1245)
opt.add(J_end - J_start >= 30)    # Meet John for at least 30 minutes

# Travel from Financial District to Alamo Square takes 17 minutes.
opt.add(J_start >= S_end + t_F_to_A)

# Optional: choose an objective that “packs” the meetings as early as possible,
# leaving the rest of the day free. Here we minimize the finish time of the last meeting.
opt.minimize(J_end)

if opt.check() == sat:
    model = opt.model()
    s_start_val = model[S_start].as_long()
    s_end_val   = model[S_end].as_long()
    j_start_val = model[J_start].as_long()
    j_end_val   = model[J_end].as_long()

    # Helper: Convert minutes to HH:MM in 24-hour format.
    def minutes_to_time(m):
        hours = m // 60
        minutes = m % 60
        return f"{hours:02d}:{minutes:02d}"
    
    itinerary = [
        {"action": "meet", "person": "Stephanie",
         "start_time": minutes_to_time(s_start_val),
         "end_time": minutes_to_time(s_end_val)},
        {"action": "meet", "person": "John",
         "start_time": minutes_to_time(j_start_val),
         "end_time": minutes_to_time(j_end_val)}
    ]
    
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=4))
else:
    print("No solution found!")