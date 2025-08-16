from z3 import *

# Helper to convert minutes after midnight to HH:MM format
def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

# Create a solver instance
s = Solver()

# We work in minutes after midnight.
# Our starting point: You arrive at Union Square at 9:00AM (9*60 = 540 minutes).

# Define meeting time variables (start and end) for each friend in the chosen ordering.
# In this schedule we plan to meet 6 friends in sequence:
# Order: Betty (at Russian Hill), then Anthony (at Chinatown), then Melissa (at Alamo Square),
# then Jeffrey (at Marina District), then Joshua (at Haight-Ashbury) and finally Emily (at Sunset District).
betty_start = Int('betty_start')
betty_end   = Int('betty_end')

anthony_start = Int('anthony_start')
anthony_end   = Int('anthony_end')

melissa_start = Int('melissa_start')
melissa_end   = Int('melissa_end')

jeffrey_start = Int('jeffrey_start')
jeffrey_end   = Int('jeffrey_end')

joshua_start = Int('joshua_start')
joshua_end   = Int('joshua_end')

emily_start = Int('emily_start')
emily_end   = Int('emily_end')

# Define friends’ availability and minimum meeting durations (all in minutes):
# Betty: available 7:00 (420) to 16:45 (1005), duration >= 105.
s.add(betty_start >= 420)
s.add(betty_end <= 1005)
s.add(betty_end - betty_start >= 105)

# Anthony: available 11:45 (705) to 13:30 (810), duration >= 75.
s.add(anthony_start >= 705)
s.add(anthony_end <= 810)
s.add(anthony_end - anthony_start >= 75)

# Melissa: available 9:30 (570) to 17:15 (1035), duration >= 105.
s.add(melissa_start >= 570)
s.add(melissa_end <= 1035)
s.add(melissa_end - melissa_start >= 105)

# Jeffrey: available 12:15 (735) to 18:00 (1080), duration >= 45.
s.add(jeffrey_start >= 735)
s.add(jeffrey_end <= 1080)
s.add(jeffrey_end - jeffrey_start >= 45)

# Joshua: available 12:15 (735) to 19:00 (1140), duration >= 90.
s.add(joshua_start >= 735)
s.add(joshua_end <= 1140)
s.add(joshua_end - joshua_start >= 90)

# Emily: available 19:30 (1170) to 21:30 (1290), duration >= 120.
# Because her window is exactly 120 minutes, we set her meeting to start at 1170 and end at 1290.
s.add(emily_start == 1170)
s.add(emily_end == 1290)

# Define travel times (in minutes) for the legs we use:
# From Union Square to Russian Hill (Betty): 13
# From Russian Hill to Chinatown (Betty -> Anthony): 9
# From Chinatown to Alamo Square (Anthony -> Melissa): 17
# From Alamo Square to Marina District (Melissa -> Jeffrey): 15
# From Marina District to Haight-Ashbury (Jeffrey -> Joshua): 16
# From Haight-Ashbury to Sunset District (Joshua -> Emily): 15

# Ordering/travel constraints:
# 1. You start at Union Square at 9:00 (540) so Betty’s meeting cannot start before 540+13.
s.add(betty_start >= 540 + 13)

# 2. Anthony must be met after Betty. So Anthony’s meeting can start no sooner than
# Betty’s end plus travel time from Russian Hill to Chinatown.
s.add(anthony_start >= betty_end + 9)

# 3. Melissa must start after finishing with Anthony plus travel from Chinatown to Alamo Square.
s.add(melissa_start >= anthony_end + 17)

# 4. Jeffrey starts after Melissa plus travel from Alamo Square to Marina District.
s.add(jeffrey_start >= melissa_end + 15)

# 5. Joshua starts after Jeffrey plus travel from Marina District to Haight-Ashbury.
s.add(joshua_start >= jeffrey_end + 16)

# 6. Emily must be met after Joshua. Because Emily’s meeting must start exactly at 19:30,
# we require that Joshua’s meeting finish and allow travel (15 minutes) by then.
s.add(emily_start >= joshua_end + 15)
s.add(joshua_end + 15 <= 1170)

# (All meeting durations are at least the specified minimum and must occur within each friend’s window.)

# Check the constraints and, if the schedule is feasible, extract the meeting times.
if s.check() == sat:
    m = s.model()
    itinerary = []
    itinerary.append({
        "action": "meet",
        "person": "Betty",
        "start_time": minutes_to_time(m[betty_start].as_long()),
        "end_time": minutes_to_time(m[betty_end].as_long())
    })
    itinerary.append({
        "action": "meet",
        "person": "Anthony",
        "start_time": minutes_to_time(m[anthony_start].as_long()),
        "end_time": minutes_to_time(m[anthony_end].as_long())
    })
    itinerary.append({
        "action": "meet",
        "person": "Melissa",
        "start_time": minutes_to_time(m[melissa_start].as_long()),
        "end_time": minutes_to_time(m[melissa_end].as_long())
    })
    itinerary.append({
        "action": "meet",
        "person": "Jeffrey",
        "start_time": minutes_to_time(m[jeffrey_start].as_long()),
        "end_time": minutes_to_time(m[jeffrey_end].as_long())
    })
    itinerary.append({
        "action": "meet",
        "person": "Joshua",
        "start_time": minutes_to_time(m[joshua_start].as_long()),
        "end_time": minutes_to_time(m[joshua_end].as_long())
    })
    itinerary.append({
        "action": "meet",
        "person": "Emily",
        "start_time": minutes_to_time(m[emily_start].as_long()),
        "end_time": minutes_to_time(m[emily_end].as_long())
    })
    
    import json
    print(json.dumps({"itinerary": itinerary}, indent=4))
else:
    print("No solution found")