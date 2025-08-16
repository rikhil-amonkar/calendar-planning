from z3 import *
import json

# We'll measure time as minutes after midnight. For reference:
#  9:00        = 9*60 = 540
# 10:30        = 10*60+30 = 630
# 11:30        = 690
#  8:00        = 480;  14:45 = 885;  7:30 = 450; 19:15 = 1155;
# 13:45 = 825; 18:45 = 1125;
# 17:30 = 1050; 20:30 = 1230; 18:45 = 1125; 21:15 = 1275

# We use the following fixed ordering (the chosen feasible route):
#   1. James    at Embarcadero (min duration 30, window: 10:30-11:30)
#   2. Anthony  at Mission District (105, window: 8:00-14:45)
#   3. Linda    at Haight-Ashbury (15, window: 7:30-19:15)
#   4. Helen    at North Beach (30, window: 13:45-18:45)
#   5. Paul     at Fisherman's Wharf (90, window: 14:45-18:45)
#   6. William  at Bayview (120, window: 17:30-20:30)
#   7. Kimberly at Golden Gate Park (75, window: 18:45-21:15)
#
# Travel times (in minutes) along the chosen route (taken from the table):
#   - Start (Russian Hill, arrival at 9:00) -> Embarcadero: 8
#   - Embarcadero -> Mission District: 20
#   - Mission District -> Haight-Ashbury: 12
#   - Haight-Ashbury -> North Beach: 19
#   - North Beach -> Fisherman's Wharf: 5
#   - Fisherman's Wharf -> Bayview: 26
#   - Bayview -> Golden Gate Park: 22
#
# We impose the constraint that the start time of each meeting (in minutes after midnight)
# must be at least the meeting's window start, and its end time (start+duration) must not exceed
# the window end. Also, for events in our fixed order, the start of the next meeting must be
# at least the (end time of previous meeting + travel time).

# Create a solver:
s = Solver()

# Create Int variables for the start times of each meeting (in minutes after midnight)
James  = Int('James')   # Embarcadero, duration 30, window [630,690]
Anthony = Int('Anthony') # Mission District, duration 105, window [480,885]
Linda  = Int('Linda')    # Haight-Ashbury, duration 15, window [450,1155]
Helen  = Int('Helen')    # North Beach, duration 30, window [825,1125]
Paul   = Int('Paul')     # Fisherman's Wharf, duration 90, window [885,1125]
William = Int('William') # Bayview, duration 120, window [1050,1230]
Kimberly = Int('Kimberly')  # Golden Gate Park, duration 75, window [1125,1275]

# Helper durations and travel times:
durations = {
    "James": 30,
    "Anthony": 105,
    "Linda": 15,
    "Helen": 30,
    "Paul": 90,
    "William": 120,
    "Kimberly": 75
}

# Availability windows: (available_from, available_to)
windows = {
    "James":    (630, 690),    # 10:30 to 11:30
    "Anthony":  (480, 885),    # 8:00 to 14:45
    "Linda":    (450, 1155),   # 7:30 to 19:15
    "Helen":    (825, 1125),   # 13:45 to 18:45
    "Paul":     (885, 1125),   # 14:45 to 18:45
    "William":  (1050, 1230),  # 17:30 to 20:30
    "Kimberly": (1125, 1275)   # 18:45 to 21:15
}

# Function to add availability constraints for a meeting:
def add_window_constraints(name, var):
    start, end = windows[name]
    s.add(var >= start)
    s.add(var + durations[name] <= end)

add_window_constraints("James", James)
add_window_constraints("Anthony", Anthony)
add_window_constraints("Linda", Linda)
add_window_constraints("Helen", Helen)
add_window_constraints("Paul", Paul)
add_window_constraints("William", William)
add_window_constraints("Kimberly", Kimberly)

# Also, we must start from Russian Hill at 9:00 = 540.
# The travel time from Russian Hill to the first meeting place (Embarcadero) is 8 minutes.
s.add(James >= 540 + 8)

# Now add ordering constraints based on the fixed route.
# Define end times for clarity:
James_end   = James + durations["James"]
Anthony_end = Anthony + durations["Anthony"]
Linda_end   = Linda + durations["Linda"]
Helen_end   = Helen + durations["Helen"]
Paul_end    = Paul + durations["Paul"]
William_end = William + durations["William"]
Kimberly_end = Kimberly + durations["Kimberly"]

# Travel times along the route:
# Embarcadero -> Mission District: 20
s.add(Anthony >= James_end + 20)

# Mission District -> Haight-Ashbury: 12
s.add(Linda >= Anthony_end + 12)

# Haight-Ashbury -> North Beach: 19
s.add(Helen >= Linda_end + 19)

# North Beach -> Fisherman's Wharf: 5
s.add(Paul >= Helen_end + 5)
# Also, meeting Paul can’t start before his window (already enforced)

# Fisherman's Wharf -> Bayview: 26
s.add(William >= Paul_end + 26)

# Bayview -> Golden Gate Park: 22
s.add(Kimberly >= William_end + 22)

# (Optional) For a "nice" schedule, we can ask the solver to try and minimize waiting times.
# Here we use a simple optimization trick: force each meeting to start as early as possible.
# For our purposes, finding any solution that satisfies these constraints is enough.

if s.check() == sat:
    m = s.model()
    schedule = {}
    schedule["James"]   = (m[James].as_long(), m[James_end].as_long())
    schedule["Anthony"] = (m[Anthony].as_long(), m[Anthony_end].as_long())
    schedule["Linda"]   = (m[Linda].as_long(), m[Linda_end].as_long())
    schedule["Helen"]   = (m[Helen].as_long(), m[Helen_end].as_long())
    schedule["Paul"]    = (m[Paul].as_long(), m[Paul_end].as_long())
    schedule["William"] = (m[William].as_long(), m[William_end].as_long())
    schedule["Kimberly"]= (m[Kimberly].as_long(), m[Kimberly_end].as_long())
else:
    raise Exception("No solution found!")

# Helper function to convert minutes (after midnight) to "HH:MM" format.
def minutes_to_HHMM(t):
    h = t // 60
    m = t % 60
    return f"{h:02d}:{m:02d}"

# Build the itinerary as a list of meeting entries.
# The order is the same as our routing order.
itinerary = []
for person in ["James", "Anthony", "Linda", "Helen", "Paul", "William", "Kimberly"]:
    start, end = schedule[person]
    entry = {
        "action": "meet",
        "person": person,
        "start_time": minutes_to_HHMM(start),
        "end_time": minutes_to_HHMM(end)
    }
    itinerary.append(entry)

# Print the final JSON-formatted itinerary.
result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))