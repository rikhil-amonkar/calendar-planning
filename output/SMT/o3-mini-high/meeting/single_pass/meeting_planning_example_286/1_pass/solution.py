from z3 import *
import json

def minutes_to_time(mins):
    hours = mins // 60
    minutes = mins % 60
    return f"{hours:02d}:{minutes:02d}"

# Create the Z3 solver
s = Solver()

# Define integer variables for start and end times (in minutes after midnight)
# Carol’s meeting (in Sunset District)
C_start = Int('C_start')
C_end   = Int('C_end')
# Karen’s meeting (in Bayview)
K_start = Int('K_start')
K_end   = Int('K_end')
# Rebecca’s meeting (in Mission District)
R_start = Int('R_start')
R_end   = Int('R_end')

# Define available time windows (in minutes after midnight)
# You arrive at Union Square at 9:00AM -> 9*60 = 540.
# Carol: available in Sunset District from 10:15 to 11:45.
carol_avail_start = 10 * 60 + 15  # 615
carol_avail_end   = 11 * 60 + 45  # 705
# Karen: available in Bayview from 12:45 to 15:00.
karen_avail_start = 12 * 60 + 45  # 765
karen_avail_end   = 15 * 60       # 900
# Rebecca: available in Mission District from 11:30 to 20:15.
rebecca_avail_start = 11 * 60 + 30  # 690
rebecca_avail_end   = 20 * 60 + 15  # 1215

# Minimum meeting durations (in minutes)
min_dur_carol = 30
min_dur_karen = 120
min_dur_rebecca = 120

# Travel times (in minutes) between locations:
# Start at Union Square at 9:00.
# Union Square -> Sunset District: 26 minutes.
# Sunset District -> Bayview: 22 minutes.
# Bayview -> Mission District: 13 minutes.
start_time = 9 * 60  # 540 minutes

# -----------------------
# Carol meeting constraints (Sunset District)
s.add(C_start >= carol_avail_start)    # must start no earlier than 10:15
s.add(C_end <= carol_avail_end)          # must finish by 11:45
s.add(C_end - C_start >= min_dur_carol)  # at least 30 minutes meeting

# Additionally, you must travel from Union Square to Sunset District.
# So the meeting can start only after start_time + 26.
s.add(C_start >= start_time + 26)

# -----------------------
# Karen meeting constraints (Bayview)
s.add(K_start >= karen_avail_start)    # not before 12:45
s.add(K_end <= karen_avail_end)        # finish by 15:00
s.add(K_end - K_start >= min_dur_karen)  # at least 120 minutes

# Travel from Carol (Sunset District) to Karen (Bayview) requires 22 minutes.
s.add(K_start >= C_end + 22)

# -----------------------
# Rebecca meeting constraints (Mission District)
s.add(R_start >= rebecca_avail_start)    # not before 11:30
s.add(R_end <= rebecca_avail_end)          # finish by 20:15
s.add(R_end - R_start >= min_dur_rebecca)  # at least 120 minutes

# Travel from Karen (Bayview) to Rebecca (Mission District) requires 13 minutes.
s.add(R_start >= K_end + 13)

# We now have fixed the ordering as:
# 1. Carol in Sunset District,
# 2. Karen in Bayview, and then
# 3. Rebecca in Mission District.
#
# The constraints ensure that all meeting start times respect the travel times
# and each meeting meets the minimum duration requirement within the friend’s available window.

if s.check() == sat:
    m = s.model()
    carol_start_val = m[C_start].as_long()
    carol_end_val   = m[C_end].as_long()
    karen_start_val = m[K_start].as_long()
    karen_end_val   = m[K_end].as_long()
    rebecca_start_val = m[R_start].as_long()
    rebecca_end_val   = m[R_end].as_long()

    itinerary = [
        {"action": "meet", "person": "Carol",
         "start_time": minutes_to_time(carol_start_val),
         "end_time": minutes_to_time(carol_end_val)},
        {"action": "meet", "person": "Karen",
         "start_time": minutes_to_time(karen_start_val),
         "end_time": minutes_to_time(karen_end_val)},
        {"action": "meet", "person": "Rebecca",
         "start_time": minutes_to_time(rebecca_start_val),
         "end_time": minutes_to_time(rebecca_end_val)}
    ]
    
    result = {"itinerary": itinerary}
    
    print("SOLUTION:")
    print(json.dumps(result, indent=2))
else:
    print("No solution found")