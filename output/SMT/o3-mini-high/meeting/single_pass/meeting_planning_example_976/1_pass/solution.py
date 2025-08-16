from z3 import *
import json

# Define friend data
# Times are in minutes after midnight.
# For example, 9:00AM = 540 minutes; 12:15PM = 735; 16:30 = 990; etc.
# Each friend: name, location, available start, available end, required meeting duration.
friends = [
    {"name": "Matthew",   "loc": "Bayview",           "avail_start": 1155, "avail_end": 1320, "duration": 120},
    {"name": "Karen",     "loc": "Chinatown",         "avail_start": 1155, "avail_end": 1275, "duration": 90},
    {"name": "Sarah",     "loc": "Alamo Square",      "avail_start": 1200, "avail_end": 1305, "duration": 105},
    {"name": "Jessica",   "loc": "Nob Hill",          "avail_start": 990,  "avail_end": 1125, "duration": 120},
    {"name": "Stephanie", "loc": "Presidio",          "avail_start": 450,  "avail_end": 615,  "duration": 60},
    {"name": "Mary",      "loc": "Union Square",      "avail_start": 1005, "avail_end": 1290, "duration": 60},
    {"name": "Charles",   "loc": "The Castro",        "avail_start": 990,  "avail_end": 1320, "duration": 105},
    {"name": "Nancy",     "loc": "North Beach",       "avail_start": 885,  "avail_end": 1200, "duration": 15},
    {"name": "Thomas",    "loc": "Fisherman's Wharf", "avail_start": 810,  "avail_end": 1140, "duration": 30},
    {"name": "Brian",     "loc": "Marina District",   "avail_start": 735,  "avail_end": 1080, "duration": 60},
]

# Define travel times (in minutes) for every ordered pair as provided.
# Note: Times are not necessarily symmetric.
travel = {}

# From Embarcadero to each location
travel[("Embarcadero", "Bayview")]           = 21
travel[("Embarcadero", "Chinatown")]         = 7
travel[("Embarcadero", "Alamo Square")]      = 19
travel[("Embarcadero", "Nob Hill")]          = 10
travel[("Embarcadero", "Presidio")]          = 20
travel[("Embarcadero", "Union Square")]      = 10
travel[("Embarcadero", "The Castro")]        = 25
travel[("Embarcadero", "North Beach")]       = 5
travel[("Embarcadero", "Fisherman's Wharf")] = 6
travel[("Embarcadero", "Marina District")]   = 12

# Bayview row
travel[("Bayview", "Embarcadero")]           = 19
travel[("Bayview", "Chinatown")]             = 19
travel[("Bayview", "Alamo Square")]          = 16
travel[("Bayview", "Nob Hill")]              = 20
travel[("Bayview", "Presidio")]              = 32
travel[("Bayview", "Union Square")]          = 18
travel[("Bayview", "The Castro")]            = 19
travel[("Bayview", "North Beach")]           = 22
travel[("Bayview", "Fisherman's Wharf")]     = 25
travel[("Bayview", "Marina District")]       = 27

# Chinatown row
travel[("Chinatown", "Embarcadero")]          = 5
travel[("Chinatown", "Bayview")]              = 20
travel[("Chinatown", "Alamo Square")]         = 17
travel[("Chinatown", "Nob Hill")]             = 9
travel[("Chinatown", "Presidio")]             = 19
travel[("Chinatown", "Union Square")]         = 7
travel[("Chinatown", "The Castro")]           = 22
travel[("Chinatown", "North Beach")]          = 3
travel[("Chinatown", "Fisherman's Wharf")]    = 8
travel[("Chinatown", "Marina District")]      = 12

# Alamo Square row
travel[("Alamo Square", "Embarcadero")]       = 16
travel[("Alamo Square", "Bayview")]           = 16
travel[("Alamo Square", "Chinatown")]         = 15
travel[("Alamo Square", "Nob Hill")]          = 11
travel[("Alamo Square", "Presidio")]          = 17
travel[("Alamo Square", "Union Square")]      = 14
travel[("Alamo Square", "The Castro")]        = 8
travel[("Alamo Square", "North Beach")]       = 15
travel[("Alamo Square", "Fisherman's Wharf")] = 19
travel[("Alamo Square", "Marina District")]   = 15

# Nob Hill row
travel[("Nob Hill", "Embarcadero")]           = 9
travel[("Nob Hill", "Bayview")]               = 19
travel[("Nob Hill", "Chinatown")]             = 6
travel[("Nob Hill", "Alamo Square")]          = 11
travel[("Nob Hill", "Presidio")]              = 17
travel[("Nob Hill", "Union Square")]          = 7
travel[("Nob Hill", "The Castro")]            = 17
travel[("Nob Hill", "North Beach")]           = 8
travel[("Nob Hill", "Fisherman's Wharf")]     = 10
travel[("Nob Hill", "Marina District")]       = 11

# Presidio row
travel[("Presidio", "Embarcadero")]           = 20
travel[("Presidio", "Bayview")]               = 31
travel[("Presidio", "Chinatown")]             = 21
travel[("Presidio", "Alamo Square")]          = 19
travel[("Presidio", "Nob Hill")]              = 18
travel[("Presidio", "Union Square")]          = 22
travel[("Presidio", "The Castro")]            = 21
travel[("Presidio", "North Beach")]           = 18
travel[("Presidio", "Fisherman's Wharf")]     = 19
travel[("Presidio", "Marina District")]       = 11

# Union Square row
travel[("Union Square", "Embarcadero")]       = 11
travel[("Union Square", "Bayview")]           = 15
travel[("Union Square", "Chinatown")]         = 7
travel[("Union Square", "Alamo Square")]      = 15
travel[("Union Square", "Nob Hill")]          = 9
travel[("Union Square", "Presidio")]          = 24
travel[("Union Square", "The Castro")]        = 17
travel[("Union Square", "North Beach")]       = 10
travel[("Union Square", "Fisherman's Wharf")] = 15
travel[("Union Square", "Marina District")]   = 18

# The Castro row
travel[("The Castro", "Embarcadero")]         = 22
travel[("The Castro", "Bayview")]             = 19
travel[("The Castro", "Chinatown")]           = 22
travel[("The Castro", "Alamo Square")]        = 8
travel[("The Castro", "Nob Hill")]            = 16
travel[("The Castro", "Presidio")]            = 20
travel[("The Castro", "Union Square")]        = 19
travel[("The Castro", "North Beach")]         = 20
travel[("The Castro", "Fisherman's Wharf")]   = 24
travel[("The Castro", "Marina District")]     = 21

# North Beach row
travel[("North Beach", "Embarcadero")]        = 6
travel[("North Beach", "Bayview")]            = 25
travel[("North Beach", "Chinatown")]          = 6
travel[("North Beach", "Alamo Square")]       = 16
travel[("North Beach", "Nob Hill")]           = 7
travel[("North Beach", "Presidio")]           = 17
travel[("North Beach", "Union Square")]       = 7
travel[("North Beach", "The Castro")]         = 23
travel[("North Beach", "Fisherman's Wharf")]  = 5
travel[("North Beach", "Marina District")]    = 9

# Fisherman's Wharf row
travel[("Fisherman's Wharf", "Embarcadero")]        = 8
travel[("Fisherman's Wharf", "Bayview")]            = 26
travel[("Fisherman's Wharf", "Chinatown")]          = 12
travel[("Fisherman's Wharf", "Alamo Square")]       = 21
travel[("Fisherman's Wharf", "Nob Hill")]           = 11
travel[("Fisherman's Wharf", "Presidio")]           = 17
travel[("Fisherman's Wharf", "Union Square")]       = 13
travel[("Fisherman's Wharf", "The Castro")]         = 27
travel[("Fisherman's Wharf", "North Beach")]        = 6
travel[("Fisherman's Wharf", "Marina District")]      = 9

# Marina District row
travel[("Marina District", "Embarcadero")]    = 14
travel[("Marina District", "Bayview")]        = 27
travel[("Marina District", "Chinatown")]      = 15
travel[("Marina District", "Alamo Square")]   = 15
travel[("Marina District", "Nob Hill")]         = 12
travel[("Marina District", "Presidio")]       = 10
travel[("Marina District", "Union Square")]   = 16
travel[("Marina District", "The Castro")]     = 22
travel[("Marina District", "North Beach")]    = 11
travel[("Marina District", "Fisherman's Wharf")] = 10

# Create Z3 optimization solver.
opt = Optimize()

n = len(friends)

# For each friend i, create:
#   X[i]: Bool variable which is True if we schedule a meeting with friend i.
#   S[i]: Int variable representing the meeting start time (in minutes).
X = [Bool(f"X_{i}") for i in range(n)]
S = [Int(f"S_{i}") for i in range(n)]
# We will assume meeting durations are fixed at the minimum required value.
# Also, we restrict S[i] to be between 0 and 24*60.
for i, f in enumerate(friends):
    # If meeting is scheduled then:
    #  - S[i] must be no earlier than the friend’s available start time and also
    #    no earlier than the time taken to get from Embarcadero.
    #  - And the meeting must finish by the friend’s available end time.
    travel_from_start = travel[("Embarcadero", f["loc"])]
    opt.add(Implies(X[i],
                    And(
                        S[i] >= f["avail_start"],
                        S[i] >= 540 + travel_from_start,  # must leave Embarcadero at 9:00 (540)
                        S[i] + f["duration"] <= f["avail_end"],
                        S[i] >= 0, S[i] <= 1440
                    )
                   ))

# For any two scheduled meetings i and j, ensure they do not overlap.
# That is, one must finish + travel to the other before the other starts.
for i in range(n):
    for j in range(i+1, n):
        # Only enforce if both meetings are scheduled.
        # Either meeting i comes before j or vice‐versa.
        ti = travel[(friends[i]["loc"], friends[j]["loc"])]
        tj = travel[(friends[j]["loc"], friends[i]["loc"])]
        # meeting finish times if scheduled:
        finish_i = S[i] + friends[i]["duration"]
        finish_j = S[j] + friends[j]["duration"]
        opt.add(Implies(And(X[i], X[j]),
                        Or(finish_i + ti <= S[j],
                           finish_j + tj <= S[i])))

# Our objective is to maximize the number of meetings scheduled.
obj = Sum([If(X[i], 1, 0) for i in range(n)])
h = opt.maximize(obj)

# Check satisfiability and get model.
if opt.check() == sat:
    mod = opt.model()
    # gather scheduled meetings with their assigned start times.
    meetings = []
    for i, f in enumerate(friends):
        if is_true(mod.evaluate(X[i])):
            start_time = mod.evaluate(S[i]).as_long()
            end_time = start_time + f["duration"]
            meetings.append({
                "person": f["name"],
                "start": start_time,
                "end": end_time,
                "loc": f["loc"]
            })

    # Sort meetings by start time.
    meetings.sort(key=lambda m: m["start"])

    # Helper function to convert minutes to HH:MM in 24-hr format.
    def to_time_str(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Build the final itinerary entries.
    itinerary = []
    for m in meetings:
        itinerary.append({
            "action": "meet",
            "person": m["person"],
            "start_time": to_time_str(m["start"]),
            "end_time": to_time_str(m["end"])
        })

    # Create output dictionary.
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))
else:
    print("No solution found")