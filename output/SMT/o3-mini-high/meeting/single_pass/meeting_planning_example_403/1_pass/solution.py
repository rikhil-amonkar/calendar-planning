from z3 import *
import json

def minutes_to_str(m):
    # Convert minutes (integer) since midnight to "HH:MM" 24-hour string.
    h = m // 60
    minute = m % 60
    return f"{h:02d}:{minute:02d}"

# Define meeting start time variables (in minutes from midnight)
# We fix an order: 
# 1. Rebecca (at Chinatown)
# 2. Andrew (at Golden Gate Park)
# 3. Robert (at The Castro)
# 4. Sarah (at Pacific Heights)
# 5. Nancy (at Presidio)

r_start = Int("r_start")   # Rebecca start time
a_start = Int("a_start")   # Andrew start time
rob_start = Int("rob_start")  # Robert start time
s_start = Int("s_start")   # Sarah start time
n_start = Int("n_start")   # Nancy start time

# Meeting durations (in minutes)
r_duration = 90   # Rebecca: 90 minutes
a_duration = 75   # Andrew: 75 minutes
rob_duration = 30 # Robert: 30 minutes
s_duration = 15   # Sarah: 15 minutes
n_duration = 60   # Nancy: 60 minutes

# Compute end times (expressions)
r_end = r_start + r_duration
a_end = a_start + a_duration
rob_end = rob_start + rob_duration
s_end = s_start + s_duration
n_end = n_start + n_duration

# Available time windows for each friend (in minutes from midnight)
# 9:45 is 585, 21:30 is 1290
# 11:45 is 705, 14:30 is 870
# 08:30 is 510, 14:15 is 855
# 16:15 is 975, 18:45 is 1125
# 17:30 is 1050, 19:15 is 1155

constraints = []

# Availability constraints:
constraints.append(r_start >= 585)
constraints.append(r_end <= 1290)

constraints.append(a_start >= 705)
constraints.append(a_end <= 870)

constraints.append(rob_start >= 510)
constraints.append(rob_end <= 855)

constraints.append(s_start >= 975)
constraints.append(s_end <= 1125)

constraints.append(n_start >= 1050)
constraints.append(n_end <= 1155)

# You arrive at Union Square at 9:00 = 540 minutes
start_time = 540

# Travel distances (in minutes) between locations – note these are directional:
# Order of meetings with locations:
#   Union Square (start) -> Chinatown (Rebecca) -> Golden Gate Park (Andrew) ->
#   The Castro (Robert) -> Pacific Heights (Sarah) -> Presidio (Nancy)
#
# From the given travel matrix:
#   Union Square to Chinatown: 7
#   Chinatown to Golden Gate Park: 23
#   Golden Gate Park to The Castro: 13
#   The Castro to Pacific Heights: 16
#   Pacific Heights to Presidio: 11

# Travel constraints:
# Must have enough time to travel after a meeting ends before the next meeting begins.
constraints.append(r_start >= start_time + 7)  # from Union Square to Chinatown

constraints.append(a_start >= r_end + 23)  # from Chinatown to Golden Gate Park

constraints.append(rob_start >= a_start + a_duration + 13)  # from Golden Gate Park to The Castro

constraints.append(s_start >= rob_start + rob_duration + 16)  # from The Castro to Pacific Heights

constraints.append(n_start >= s_start + s_duration + 11)  # from Pacific Heights to Presidio

# Set up the Z3 solver and add the constraints
solver = Solver()
for c in constraints:
    solver.add(c)

if solver.check() == sat:
    m = solver.model()
    
    # Extract solution values (in minutes since midnight)
    r_val = m[r_start].as_long()
    a_val = m[a_start].as_long()
    rob_val = m[rob_start].as_long()
    s_val = m[s_start].as_long()
    n_val = m[n_start].as_long()
    
    itinerary = [
        {
            "action": "meet",
            "person": "Rebecca",
            "start_time": minutes_to_str(r_val),
            "end_time": minutes_to_str(r_val + r_duration)
        },
        {
            "action": "meet",
            "person": "Andrew",
            "start_time": minutes_to_str(a_val),
            "end_time": minutes_to_str(a_val + a_duration)
        },
        {
            "action": "meet",
            "person": "Robert",
            "start_time": minutes_to_str(rob_val),
            "end_time": minutes_to_str(rob_val + rob_duration)
        },
        {
            "action": "meet",
            "person": "Sarah",
            "start_time": minutes_to_str(s_val),
            "end_time": minutes_to_str(s_val + s_duration)
        },
        {
            "action": "meet",
            "person": "Nancy",
            "start_time": minutes_to_str(n_val),
            "end_time": minutes_to_str(n_val + n_duration)
        }
    ]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    print("No solution found")