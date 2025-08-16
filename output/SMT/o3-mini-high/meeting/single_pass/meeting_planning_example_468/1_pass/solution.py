from z3 import Int, Solver, sat
import json

# We represent times as minutes from midnight.
# Our fixed starting “home” is The Castro at 9:00, which is 9*60 = 540 minutes.
# For each friend we create an integer variable for the meeting start time, and we assume
# that each meeting lasts exactly 90 minutes.
#
# Friends and their locations (with travel times given below):
#   • Rebecca is at Bayview (available 9:00–12:45 → [540, 765]) 
#   • Melissa is at Golden Gate Park (available 9:00–18:45 → [540, 1125])
#   • James is at Alamo Square (available 9:45–21:15 → [585, 1275])
#   • Sarah is at Fisherman's Wharf (available 8:00–21:30 → [480, 1290])
#   • Amanda is at Pacific Heights (available 18:30–21:45 → [1110, 1305])
#
# Our travel times (in minutes) are given between locations.
# Our chosen ordering (with travel legs calculated) is:
#   Castro (start @540) -> Rebecca (Bayview) -> Melissa (Golden Gate Park) ->
#   James (Alamo Square) -> Sarah (Fisherman's Wharf) -> Amanda (Pacific Heights)
#
# Travel times used in our route:
#   • Castro to Bayview:         19 minutes.
#   • Bayview to Golden Gate Park: 22 minutes.
#   • Golden Gate Park to Alamo Square: 10 minutes.
#   • Alamo Square to Fisherman's Wharf: 19 minutes.
#   • Fisherman's Wharf to Pacific Heights: 12 minutes.
#
# We then add the following constraints on each friend’s meeting start time (t) so that:
# 1. You arrive at the friend’s location no earlier than the travel time required.
# 2. The meeting (lasting 90 minutes) falls within the friend’s availability.
# 3. The ordering is preserved including travel time between meetings.

# Create solver
solver = Solver()

# Define meeting start time variables (in minutes from midnight)
r = Int("r")  # Rebecca at Bayview
m = Int("m")  # Melissa at Golden Gate Park
j = Int("j")  # James at Alamo Square
s = Int("s")  # Sarah at Fisherman's Wharf
a = Int("a")  # Amanda at Pacific Heights

# Constraint for Rebecca:
# You start at Castro at 9:00 (540) and ride to Bayview (19 minutes).
# So you cannot start meeting Rebecca before 540+19 = 559.
# Also Rebecca leaves at 12:45 (765), and since the meeting lasts 90 minutes, r+90 <= 765.
solver.add(r >= 540 + 19)
solver.add(r + 90 <= 765)

# Constraint for Melissa:
# After finishing with Rebecca you must travel from Bayview to Golden Gate Park (22 min):
#   m >= r + 90 + 22.
# Melissa is available only until 18:45 (1125 minutes), so m+90 <= 1125.
solver.add(m >= r + 90 + 22)
solver.add(m + 90 <= 1125)

# Constraint for James:
# Travel from Golden Gate Park to Alamo Square takes 10 minutes:
#   j >= m + 90 + 10.
# James is available from 9:45 (585) and until 21:15 (1275), so j must be >=585 and j+90 <=1275.
solver.add(j >= m + 90 + 10)
solver.add(j >= 585)
solver.add(j + 90 <= 1275)

# Constraint for Sarah:
# From Alamo Square to Fisherman's Wharf takes 19 minutes:
#   s >= j + 90 + 19.
# Sarah is available until 21:30 (1290), so s+90 <=1290.
solver.add(s >= j + 90 + 19)
solver.add(s + 90 <= 1290)
# (Sarah's start must also be no earlier than her availability start at 8:00 (480), though that is implicit here)
solver.add(s >= 480)

# Constraint for Amanda:
# From Fisherman's Wharf to Pacific Heights takes 12 minutes:
#   a >= s + 90 + 12.
# Amanda is only available starting at 18:30 (1110) and until 21:45 (1305), so a must be:
#   a >= 1110 and a + 90 <= 1305.
solver.add(a >= s + 90 + 12)
solver.add(a >= 1110)
solver.add(a + 90 <= 1305)

# Check if constraints are satisfiable:
if solver.check() == sat:
    model = solver.model()
    # Get the meeting times from the model.
    r_val = model[r].as_long()
    m_val = model[m].as_long()
    j_val = model[j].as_long()
    s_val = model[s].as_long()
    a_val = model[a].as_long()
    
    # Function to format minutes from midnight into 24-hour "HH:MM" string.
    def minutes_to_str(minutes_total):
        hours = minutes_total // 60
        minutes = minutes_total % 60
        return f"{hours:02d}:{minutes:02d}"
    
    # Build the itinerary list.
    itinerary = []
    itinerary.append({
        "action": "meet", 
        "person": "Rebecca", 
        "start_time": minutes_to_str(r_val), 
        "end_time": minutes_to_str(r_val + 90)
    })
    itinerary.append({
        "action": "meet", 
        "person": "Melissa", 
        "start_time": minutes_to_str(m_val), 
        "end_time": minutes_to_str(m_val + 90)
    })
    itinerary.append({
        "action": "meet", 
        "person": "James", 
        "start_time": minutes_to_str(j_val), 
        "end_time": minutes_to_str(j_val + 90)
    })
    itinerary.append({
        "action": "meet", 
        "person": "Sarah", 
        "start_time": minutes_to_str(s_val), 
        "end_time": minutes_to_str(s_val + 90)
    })
    itinerary.append({
        "action": "meet", 
        "person": "Amanda", 
        "start_time": minutes_to_str(a_val), 
        "end_time": minutes_to_str(a_val + 90)
    })
    
    # Output the final itinerary as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=4))
else:
    print("No solution found!")