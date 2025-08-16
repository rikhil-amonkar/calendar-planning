from z3 import *
import json

def minutes_to_time(m):
    # Convert minutes since midnight into a HH:MM string.
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

# -----------------------------
# Data definitions
# -----------------------------
# Availability windows (in minutes from midnight):
#   - For example: 9:00 AM = 540, 10:30 AM = 630, 20:00 = 1200.
avail = {
    "Sandra": (420, 1200),      # Pacific Heights, available 07:00-20:00
    "Kenneth": (645, 780),      # Marina District, available 10:45-13:00
    "Robert": (600, 900),       # Fisherman's Wharf, 10:00-15:00
    "Elizabeth": (630, 1200),   # Mission District, 10:30-20:00
    "Kimberly": (615, 1095),    # Sunset District, 10:15-18:15
    "Amanda": (465, 1125),      # Golden Gate Park, 07:45-18:45
    "David": (915, 1140),       # Union Square, 15:15-19:00
    "Melissa": (1095, 1200),    # Richmond District, 18:15-20:00
    "Thomas": (1170, 1230)      # Bayview, 19:30-20:30
}

# Required meeting durations (in minutes)
durations = {
    "Sandra": 120,
    "Kenneth": 45,
    "Robert": 15,
    "Elizabeth": 90,
    "Kimberly": 105,
    "Amanda": 15,
    "David": 45,
    "Melissa": 15,
    "Thomas": 30
}

# The district where each friend is located.
location = {
    "Sandra": "Pacific Heights",
    "Kenneth": "Marina District",
    "Robert": "Fisherman's Wharf",
    "Elizabeth": "Mission District",
    "Kimberly": "Sunset District",
    "Amanda": "Golden Gate Park",
    "David": "Union Square",
    "Melissa": "Richmond District",
    "Thomas": "Bayview"
}

# Travel time (in minutes) between various San Francisco districts.
# (Only the pairs needed in our chosen route are listed below.)
travel_times = {
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Union Square"): 19,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Haight-Ashbury", "Bayview"): 18,
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Richmond District"): 10,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    
    ("Pacific Heights", "Marina District"): 6,
    ("Marina District", "Fisherman's Wharf"): 10,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Mission District", "Sunset District"): 24,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Golden Gate Park", "Union Square"): 22,
    ("Union Square", "Richmond District"): 20,
    ("Richmond District", "Bayview"): 27
}

# -----------------------------
# Chosen Order of Meetings
# -----------------------------
# Based on exploring different orders, one feasible and “optimal” route meeting all friends is:
# 1. Sandra (Pacific Heights)
# 2. Kenneth (Marina District)
# 3. Robert (Fisherman's Wharf)
# 4. Elizabeth (Mission District)
# 5. Kimberly (Sunset District)
# 6. Amanda (Golden Gate Park)
# 7. David (Union Square)
# 8. Melissa (Richmond District)
# 9. Thomas (Bayview)
order = ["Sandra", "Kenneth", "Robert", "Elizabeth", "Kimberly", "Amanda", "David", "Melissa", "Thomas"]

# -----------------------------
# Z3 Model Setup
# -----------------------------
solver = Solver()

# Create an Int variable for each meeting’s start time (minutes since midnight)
meeting_start = { person: Int(f"start_{person}") for person in order }

# Each meeting must be scheduled within that friend's availability window.
for person in order:
    avail_start, avail_end = avail[person]
    duration = durations[person]
    solver.add(meeting_start[person] >= avail_start)
    solver.add(meeting_start[person] + duration <= avail_end)

# Our day starts at Haight-Ashbury at 9:00 AM (540).
# The first meeting (with Sandra in Pacific Heights) cannot start before arriving there.
first_person = order[0]
first_location = location[first_person]
# Travel time from Haight-Ashbury to the first friend’s district:
solver.add(meeting_start[first_person] >= 540 + travel_times[("Haight-Ashbury", first_location)])

# For each consecutive pair in the fixed order, add travel and meeting duration constraints.
for i in range(1, len(order)):
    prev = order[i-1]
    curr = order[i]
    prev_loc = location[prev]
    curr_loc = location[curr]
    travel_key = (prev_loc, curr_loc)
    # Add constraint: the start time for the current meeting must be no earlier than:
    # (previous meeting’s start + duration + travel time from previous to current)
    solver.add(meeting_start[curr] >= meeting_start[prev] + durations[prev] + travel_times[travel_key])

# -----------------------------
# Solve the constraints
# -----------------------------
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for person in order:
        start_t = model[meeting_start[person]].as_long()
        end_t = start_t + durations[person]
        itinerary.append({
            "action": "meet",
            "person": person,
            "start_time": minutes_to_time(start_t),
            "end_time": minutes_to_time(end_t)
        })
    result = {"itinerary": itinerary}
    print("SOLUTION:")
    print(json.dumps(result, indent=4))
else:
    print("No solution found")