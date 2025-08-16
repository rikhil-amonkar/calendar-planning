from z3 import *
import json

# Minutes after midnight for times: for example, 9:00am = 540.
FD_start = 540  # Arrival at the Financial District at 9:00

# Travel times (in minutes) between locations.
# (origin, destination): travel time
travel = {
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Chinatown", "Union Square"): 7,
    ("Union Square", "North Beach"): 10
}

# Friend availability windows (in minutes after midnight) and required meeting durations.
#   Rebecca: at Fisherman's Wharf from 8:00 (480) to 11:15 (675), min 30 minutes.
#   Stephanie: at Golden Gate Park from 11:00 (660) to 15:00 (900), min 105 minutes.
#   Karen: at Chinatown from 13:45 (825) to 16:30 (990), min 15 minutes.
#   Brian: at Union Square from 15:00 (900) to 17:15 (1035), min 30 minutes.
#   Steven: at North Beach from 14:30 (870) to 20:45 (1245), min 120 minutes.

# We plan an itinerary in the order:
#   1. Rebecca (Fisherman's Wharf)
#   2. Stephanie (Golden Gate Park)
#   3. Karen (Chinatown)
#   4. Brian (Union Square)
#   5. Steven (North Beach)
# We must also account for travel time:
#   FD -> Fisherman's Wharf, then:
#   Fisherman's Wharf -> Golden Gate Park
#   Golden Gate Park -> Chinatown
#   Chinatown -> Union Square
#   Union Square -> North Beach

# Declare Z3 integer variables for each meeting's start and end time.
s_rebecca = Int("s_rebecca")
e_rebecca = Int("e_rebecca")

s_stephanie = Int("s_stephanie")
e_stephanie = Int("e_stephanie")

s_karen = Int("s_karen")
e_karen = Int("e_karen")

s_brian = Int("s_brian")
e_brian = Int("e_brian")

s_steven = Int("s_steven")
e_steven = Int("e_steven")

solver = Solver()

# -------------------------------------------------------------------
# Add constraints for each friend based on their available windows and minimum meeting durations.

# Rebecca is at Fisherman's Wharf.
# She is available from 8:00 (480) to 11:15 (675) but we cannot reach before FD_start + travel.
# FD -> Fisherman's Wharf travel = 10 minutes ⇒ arrival >= 540 + 10 = 550.
solver.add(s_rebecca >= 550)
solver.add(e_rebecca <= 675)
solver.add(e_rebecca - s_rebecca >= 30)

# Stephanie is at Golden Gate Park.
# Available from 11:00 (660) to 15:00 (900) and needs 105 minutes.
# Also, you must travel from Fisherman's Wharf to Golden Gate Park (25 minutes)
solver.add(s_stephanie >= 660)
solver.add(e_stephanie <= 900)
solver.add(e_stephanie - s_stephanie >= 105)
solver.add(s_stephanie >= e_rebecca + travel[("Fisherman's Wharf", "Golden Gate Park")])

# Karen is at Chinatown.
# Available from 13:45 (825) to 16:30 (990) with at least 15 minutes.
# Must travel from Golden Gate Park to Chinatown (23 minutes)
solver.add(s_karen >= 825)
solver.add(e_karen <= 990)
solver.add(e_karen - s_karen >= 15)
solver.add(s_karen >= e_stephanie + travel[("Golden Gate Park", "Chinatown")])

# Brian is at Union Square.
# Available from 15:00 (900) to 17:15 (1035) with at least 30 minutes.
# Must travel from Chinatown to Union Square (7 minutes)
solver.add(s_brian >= 900)
solver.add(e_brian <= 1035)
solver.add(e_brian - s_brian >= 30)
solver.add(s_brian >= e_karen + travel[("Chinatown", "Union Square")])

# Steven is at North Beach.
# Available from 14:30 (870) to 20:45 (1245) with at least 120 minutes.
# Must travel from Union Square to North Beach (10 minutes)
solver.add(s_steven >= 870)
solver.add(e_steven <= 1245)
solver.add(e_steven - s_steven >= 120)
solver.add(s_steven >= e_brian + travel[("Union Square", "North Beach")])

# -------------------------------------------------------------------
# Solve for a schedule that meets all constraints.
if solver.check() == sat:
    m = solver.model()
    
    # Convert integer times from minutes to HH:MM format.
    def minutes_to_time(mnts):
        hours = mnts // 60
        mins = mnts % 60
        return f"{hours:02d}:{mins:02d}"
    
    rep_start = m[s_rebecca].as_long()
    rep_end = m[e_rebecca].as_long()
    steph_start = m[s_stephanie].as_long()
    steph_end = m[e_stephanie].as_long()
    karen_start = m[s_karen].as_long()
    karen_end = m[e_karen].as_long()
    brian_start = m[s_brian].as_long()
    brian_end = m[e_brian].as_long()
    steven_start = m[s_steven].as_long()
    steven_end = m[e_steven].as_long()
    
    itinerary = [
        {"action": "meet", "person": "Rebecca",
         "start_time": minutes_to_time(rep_start), "end_time": minutes_to_time(rep_end)},
        {"action": "meet", "person": "Stephanie",
         "start_time": minutes_to_time(steph_start), "end_time": minutes_to_time(steph_end)},
        {"action": "meet", "person": "Karen",
         "start_time": minutes_to_time(karen_start), "end_time": minutes_to_time(karen_end)},
        {"action": "meet", "person": "Brian",
         "start_time": minutes_to_time(brian_start), "end_time": minutes_to_time(brian_end)},
        {"action": "meet", "person": "Steven",
         "start_time": minutes_to_time(steven_start), "end_time": minutes_to_time(steven_end)}
    ]
    
    result = {"itinerary": itinerary}
    print("SOLUTION:")
    print(json.dumps(result, indent=2))
else:
    print("No solution found")