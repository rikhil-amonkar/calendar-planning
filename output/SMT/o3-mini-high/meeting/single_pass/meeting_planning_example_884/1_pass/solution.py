from z3 import *
import json

# Define friend information (times in minutes since midnight)
# Note: 9:00AM = 540, etc.
friends = [
    {"name": "Robert",   "location": "Chinatown",          "avail_start": 465,  "avail_end": 1050, "min_duration": 120},
    {"name": "David",    "location": "Sunset District",    "avail_start": 750,  "avail_end": 1185, "min_duration": 45},
    {"name": "Matthew",  "location": "Alamo Square",       "avail_start": 525,  "avail_end": 825,  "min_duration": 90},
    {"name": "Jessica",  "location": "Financial District", "avail_start": 570,  "avail_end": 1125, "min_duration": 45},
    {"name": "Melissa",  "location": "North Beach",        "avail_start": 435,  "avail_end": 1005, "min_duration": 45},
    {"name": "Mark",     "location": "Embarcadero",        "avail_start": 915,  "avail_end": 1020, "min_duration": 45},
    {"name": "Deborah",  "location": "Presidio",           "avail_start": 1140, "avail_end": 1185, "min_duration": 45},
    {"name": "Karen",    "location": "Golden Gate Park",   "avail_start": 1170, "avail_end": 1320, "min_duration": 120},
    {"name": "Laura",    "location": "Bayview",            "avail_start": 1275, "avail_end": 1335, "min_duration": 15},
]

# Travel times (in minutes) between locations (keys: (from, to))
travel = {
    ("Richmond District", "Chinatown"): 20,
    ("Richmond District", "Sunset District"): 11,
    ("Richmond District", "Alamo Square"): 13,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "North Beach"): 17,
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Bayview"): 27,

    ("Chinatown", "Richmond District"): 20,
    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Financial District"): 5,
    ("Chinatown", "North Beach"): 3,
    ("Chinatown", "Embarcadero"): 5,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Bayview"): 20,

    ("Sunset District", "Richmond District"): 12,
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "North Beach"): 28,
    ("Sunset District", "Embarcadero"): 30,
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Bayview"): 22,

    ("Alamo Square", "Richmond District"): 11,
    ("Alamo Square", "Chinatown"): 15,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Embarcadero"): 16,
    ("Alamo Square", "Presidio"): 17,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "Bayview"): 16,

    ("Financial District", "Richmond District"): 21,
    ("Financial District", "Chinatown"): 5,
    ("Financial District", "Sunset District"): 30,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "North Beach"): 7,
    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "Presidio"): 22,
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Bayview"): 19,

    ("North Beach", "Richmond District"): 18,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Sunset District"): 27,
    ("North Beach", "Alamo Square"): 16,
    ("North Beach", "Financial District"): 8,
    ("North Beach", "Embarcadero"): 6,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Bayview"): 25,

    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "Chinatown"): 7,
    ("Embarcadero", "Sunset District"): 30,
    ("Embarcadero", "Alamo Square"): 19,
    ("Embarcadero", "Financial District"): 5,
    ("Embarcadero", "North Beach"): 5,
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Bayview"): 21,

    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "Alamo Square"): 19,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Bayview"): 31,

    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Alamo Square"): 9,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "North Beach"): 23,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Bayview"): 23,

    ("Bayview", "Richmond District"): 25,
    ("Bayview", "Chinatown"): 19,
    ("Bayview", "Sunset District"): 23,
    ("Bayview", "Alamo Square"): 16,
    ("Bayview", "Financial District"): 19,
    ("Bayview", "North Beach"): 22,
    ("Bayview", "Embarcadero"): 19,
    ("Bayview", "Presidio"): 32,
    ("Bayview", "Golden Gate Park"): 22,
}

# Create Z3 optimizer instance
opt = Optimize()

# Decision variables for each friend: meeting start time, end time and a Boolean if scheduled.
s_vars = {}
e_vars = {}
b_vars = {}
for i, f in enumerate(friends):
    # Create integer variables for start and end times
    s_vars[i] = Int("s_%d" % i)
    e_vars[i] = Int("e_%d" % i)
    # Boolean variable indicating if we decide to meet friend i
    b_vars[i] = Bool("b_%d" % i)

# The starting point is Richmond District at 9:00AM (540 minutes).
start_location = "Richmond District"
start_time = 540

# For each friend, add constraints regarding availability and travel from the starting location.
for i, f in enumerate(friends):
    # Lower bound: meeting can start only after friend is available AND after travel from Richmond District.
    travel_from_start = travel[(start_location, f["location"])]
    lower_bound = If(start_time + travel_from_start > f["avail_start"], 
                     start_time + travel_from_start, f["avail_start"])
    # Upper bound: meeting must finish by avail_end, so start <= avail_end - min_duration.
    upper_bound = f["avail_end"] - f["min_duration"]
    # If scheduled, restrict start time and meeting duration (=min_duration chosen exactly)
    opt.add(Implies(b_vars[i], s_vars[i] >= lower_bound))
    opt.add(Implies(b_vars[i], s_vars[i] <= upper_bound))
    # Fix meeting duration to the minimum required if scheduled.
    opt.add(Implies(b_vars[i], e_vars[i] == s_vars[i] + f["min_duration"]))
    # Also, meeting must finish by avail_end.
    opt.add(Implies(b_vars[i], e_vars[i] <= f["avail_end"]))

# For any two meetings that are scheduled, enforce non-overlap with required travel time between locations.
n = len(friends)
for i in range(n):
    for j in range(i+1, n):
        loc_i = friends[i]["location"]
        loc_j = friends[j]["location"]
        travel_i_to_j = travel[(loc_i, loc_j)]
        travel_j_to_i = travel[(loc_j, loc_i)]
        # If both meetings i and j are scheduled then one must occur before the other (with travel time gap).
        opt.add(Implies(And(b_vars[i], b_vars[j]),
                        Or(s_vars[i] + travel_i_to_j <= s_vars[j],
                           s_vars[j] + travel_j_to_i <= s_vars[i])))

# Objective: maximize the number of meetings scheduled.
opt_obj = Sum([If(b_vars[i], 1, 0) for i in range(n)])
opt.maximize(opt_obj)

# Check and extract a solution.
if opt.check() == sat:
    model = opt.model()
    scheduled_meetings = []
    # Collect scheduled meetings along with their computed start times in the model.
    for i, f in enumerate(friends):
        if is_true(model[b_vars[i]]):
            meeting_start = model[s_vars[i]].as_long()
            meeting_end   = model[e_vars[i]].as_long()
            scheduled_meetings.append({
                "person": f["name"],
                "location": f["location"],
                "start": meeting_start,
                "end": meeting_end
            })
    # Order the meetings by start time.
    scheduled_meetings.sort(key=lambda x: x["start"])
    
    # Helper function to convert minutes to HH:MM (24-hour format)
    def to_HHMM(m):
        hh = m // 60
        mm = m % 60
        return f"{hh:02d}:{mm:02d}"
    
    # Build itinerary entries in required format.
    itinerary = []
    for meeting in scheduled_meetings:
        itinerary.append({
            "action": "meet",
            "person": meeting["person"],
            "start_time": to_HHMM(meeting["start"]),
            "end_time": to_HHMM(meeting["end"])
        })
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    print("No solution found!")