from z3 import *
import json

# We'll measure times in minutes from midnight.
# For example, 9:00AM = 540, 14:30 = 870, etc.

# Data for each friend (meeting must occur entirely within the available window, and last at least the required duration)
# Times are given as: available start, available end, and required duration.
meetings = [
    {
        "person": "Elizabeth",
        "location": "Marina District",
        "avail_start": 510,   # 08:30
        "avail_end": 795,     # 13:15
        "duration": 105
    },
    {
        "person": "Brian",
        "location": "Presidio",
        "avail_start": 615,   # 10:15
        "avail_end": 1020,    # 17:00
        "duration": 30
    },
    {
        "person": "Sandra",
        "location": "Richmond District",
        "avail_start": 480,   # 08:00
        "avail_end": 915,     # 15:15
        "duration": 30
    },
    {
        "person": "Helen",
        "location": "Golden Gate Park",
        "avail_start": 690,   # 11:30
        "avail_end": 1305,    # 21:45
        "duration": 120
    },
    {
        "person": "Laura",
        "location": "Alamo Square",
        "avail_start": 870,   # 14:30
        "avail_end": 975,     # 16:15
        "duration": 75
    },
    {
        "person": "Mary",
        "location": "Embarcadero",
        "avail_start": 1005,  # 16:45
        "avail_end": 1125,    # 18:45
        "duration": 120
    },
    {
        "person": "Deborah",
        "location": "Financial District",
        "avail_start": 1140,  # 19:00
        "avail_end": 1245,    # 20:45
        "duration": 105
    }
]

# Our chosen order (that maximizes the number of friends met) is:
# 1. Elizabeth (Marina District)
# 2. Brian   (Presidio)
# 3. Sandra  (Richmond District)
# 4. Helen   (Golden Gate Park)
# 5. Laura   (Alamo Square)
# 6. Mary    (Embarcadero)
# 7. Deborah (Financial District)

# The starting point is the Mission District at 9:00 (540 minutes)
start_location = "Mission District"
start_time = 540  # 9:00AM

# For the purposes of our schedule we only need the travel times between the locations that are used in our itinerary.
# The provided travel times (in minutes) for our sequence are:
#   Mission District -> Marina District:       19
#   Marina District   -> Presidio:              10
#   Presidio          -> Richmond District:      7
#   Richmond District -> Golden Gate Park:       9
#   Golden Gate Park  -> Alamo Square:           9
#   Alamo Square      -> Embarcadero:           16
#   Embarcadero       -> Financial District:     5
travel_times = [
    ("Mission District", "Marina District", 19),
    ("Marina District",   "Presidio",          10),
    ("Presidio",          "Richmond District",  7),
    ("Richmond District", "Golden Gate Park",    9),
    ("Golden Gate Park",  "Alamo Square",        9),
    ("Alamo Square",      "Embarcadero",        16),
    ("Embarcadero",       "Financial District",  5)
]

# Create a Z3 solver
solver = Solver()

n = len(meetings)
# Create an integer variable for the start time of each meeting
start_vars = [Int("start_%d" % i) for i in range(n)]

# Add constraints for each meeting:
for i, m in enumerate(meetings):
    # Meeting must start no earlier than the friend’s available start.
    solver.add(start_vars[i] >= m["avail_start"])
    # The meeting (start time + required duration) must finish by the friend’s available end.
    solver.add(start_vars[i] + m["duration"] <= m["avail_end"])

# First meeting: account for travel from Mission District to the first meeting's location.
# Look up the travel time from Mission District to the first meeting's location.
for (orig, dest, t) in travel_times:
    if orig == start_location and dest == meetings[0]["location"]:
        # We must arrive at or after (start_time + travel_time)
        solver.add(start_vars[0] >= start_time + t)
        break

# Add travel constraints between consecutive meetings.
for i in range(n - 1):
    # For the pair meetings[i] -> meetings[i+1] use the matching travel time.
    travel_t = None
    for (orig, dest, t) in travel_times:
        if orig == meetings[i]["location"] and dest == meetings[i+1]["location"]:
            travel_t = t
            break
    if travel_t is None:
        raise Exception("Missing travel time from %s to %s" % (meetings[i]["location"], meetings[i+1]["location"]))
    # Constraint: finish current meeting plus travel time must be no later than the start time of the next meeting.
    solver.add(start_vars[i] + meetings[i]["duration"] + travel_t <= start_vars[i+1])

# (Optional) You could add an objective here if you wanted to select a subset.
# In this example we use a predetermined order that meets 7 friends.

if solver.check() == sat:
    model = solver.model()
    
    def format_time(t):
        # Format minutes (an integer) into HH:MM 24-hour format.
        hour = t // 60
        minute = t % 60
        return f"{hour:02d}:{minute:02d}"
    
    itinerary = []
    for i, m_data in enumerate(meetings):
        st = model[start_vars[i]].as_long()
        et = st + m_data["duration"]
        itinerary.append({
            "action": "meet",
            "person": m_data["person"],
            "start_time": format_time(st),
            "end_time": format_time(et)
        })
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=4))
else:
    print("No solution found")