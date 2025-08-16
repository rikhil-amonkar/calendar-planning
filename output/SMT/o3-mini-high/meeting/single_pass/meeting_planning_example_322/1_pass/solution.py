from z3 import Int, Solver, sat
import json

def minutes_to_time(total_minutes):
    hours = total_minutes // 60
    minutes = total_minutes % 60
    return f"{hours:02d}:{minutes:02d}"

# Create a Z3 solver instance
solver = Solver()

# Define integer variables for the meeting start times (in minutes since midnight)
# We assume time is expressed in minutes (e.g. 9:00AM is 540).
m_meet = Int("m_meet")  # Michelle meeting (Chinatown)
r_meet = Int("r_meet")  # Robert meeting (Fisherman's Wharf)
g_meet = Int("g_meet")  # George meeting (Presidio)
w_meet = Int("w_meet")  # William meeting (Russian Hill)

# Meeting durations (in minutes)
dur_m = 15   # Michelle: minimum 15 minutes
dur_r = 30   # Robert: minimum 30 minutes
dur_g = 30   # George: minimum 30 minutes
dur_w = 105  # William: minimum 105 minutes

# Availability windows (in minutes since midnight)
# Michelle in Chinatown: 8:15 (495) to 14:00 (840)
# Robert at Fisherman's Wharf: 9:00 (540) to 13:45 (825)
# George at Presidio: 10:30 (630) to 18:45 (1125)
# William at Russian Hill: 18:30 (1110) to 20:45 (1245)

# Travel times between locations (in minutes):
# From Sunset District (starting point at 9:00, 540) we use:
#   Sunset -> Chinatown = 30 minutes.
#   Chinatown -> Fisherman's Wharf = 8 minutes.
#   Fisherman's Wharf -> Presidio = 17 minutes.
#   Presidio -> Russian Hill = 14 minutes.

# Michelle meeting at Chinatown:
# We start at Sunset District at 9:00 (540) and must allow 30 minutes travel.
solver.add(m_meet >= 540 + 30)        # m_meet >= 570 (i.e. 09:30)
solver.add(m_meet >= 495)             # also within Michelle's availability
solver.add(m_meet + dur_m <= 840)       # must finish by 14:00

# Robert meeting at Fisherman's Wharf:
# After Michelle, travel from Chinatown to Fisherman's Wharf takes 8 minutes.
solver.add(r_meet >= m_meet + dur_m + 8)  # r_meet >= m_meet + 15 + 8 = m_meet + 23
solver.add(r_meet >= 540)               # available from 9:00
solver.add(r_meet + dur_r <= 825)         # must finish by 13:45

# George meeting at Presidio:
# After Robert, travel from Fisherman's Wharf to Presidio takes 17 minutes.
solver.add(g_meet >= r_meet + dur_r + 17)  # g_meet >= r_meet + 30 + 17 = r_meet + 47
solver.add(g_meet >= 630)               # available from 10:30
solver.add(g_meet + dur_g <= 1125)        # must finish by 18:45

# William meeting at Russian Hill:
# After George, travel from Presidio to Russian Hill takes 14 minutes.
solver.add(w_meet >= g_meet + dur_g + 14)  # w_meet >= g_meet + 30 + 14 = g_meet + 44
solver.add(w_meet >= 1110)             # available from 18:30 (1110)
solver.add(w_meet + dur_w <= 1245)         # must finish by 20:45

# Solve the constraints
if solver.check() == sat:
    model = solver.model()
    m_start = model[m_meet].as_long()
    r_start = model[r_meet].as_long()
    g_start = model[g_meet].as_long()
    w_start = model[w_meet].as_long()

    itinerary = [
        {"action": "meet", "person": "Michelle", "start_time": minutes_to_time(m_start), "end_time": minutes_to_time(m_start + dur_m)},
        {"action": "meet", "person": "Robert",   "start_time": minutes_to_time(r_start), "end_time": minutes_to_time(r_start + dur_r)},
        {"action": "meet", "person": "George",   "start_time": minutes_to_time(g_start), "end_time": minutes_to_time(g_start + dur_g)},
        {"action": "meet", "person": "William",  "start_time": minutes_to_time(w_start), "end_time": minutes_to_time(w_start + dur_w)}
    ]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=4))
else:
    print("No solution found.")