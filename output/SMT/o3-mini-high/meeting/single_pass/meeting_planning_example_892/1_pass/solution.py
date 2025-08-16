from z3 import Optimize, Int, If, Implies, And, sat
import json

def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

# Data for each friend.
# Times are in minutes from midnight.
# Each friend is represented as:
#   person: { district, avail_start, avail_end, duration }
# where avail_start and avail_end denote the friend’s available window
# and duration is the minimum meeting duration.
friend_info = {
    "Charles":   {"district": "Bayview",       "avail_start": 690,  "avail_end": 870,  "duration": 45},   # 11:30-14:30
    "Robert":    {"district": "Sunset District", "avail_start": 1005, "avail_end": 1260, "duration": 30},   # 16:45-21:00
    "Karen":     {"district": "Richmond District", "avail_start": 1155, "avail_end": 1290, "duration": 60},  # 19:15-21:30
    "Rebecca":   {"district": "Nob Hill",      "avail_start": 975,  "avail_end": 1230, "duration": 90},   # 16:15-20:30
    "Margaret":  {"district": "Chinatown",     "avail_start": 855,  "avail_end": 1185, "duration": 120},  # 14:15-19:45
    "Patricia":  {"district": "Haight-Ashbury","avail_start": 870,  "avail_end": 1230, "duration": 45},   # 14:30-20:30
    "Mark":      {"district": "North Beach",   "avail_start": 840,  "avail_end": 1110, "duration": 105},  # 14:00-18:30
    "Melissa":   {"district": "Russian Hill",  "avail_start": 780,  "avail_end": 1185, "duration": 30},   # 13:00-19:45
    "Laura":     {"district": "Embarcadero",   "avail_start": 465,  "avail_end": 795,  "duration": 105},  # 07:45-13:15
}

# Travel time (in minutes) between districts.
# Note: the travel times are directional.
travel = {}
# From Marina District
travel[("Marina District", "Bayview")]         = 27
travel[("Marina District", "Sunset District")]   = 19
travel[("Marina District", "Richmond District")] = 11
travel[("Marina District", "Nob Hill")]          = 12
travel[("Marina District", "Chinatown")]         = 15
travel[("Marina District", "Haight-Ashbury")]    = 16
travel[("Marina District", "North Beach")]       = 11
travel[("Marina District", "Russian Hill")]      = 8
travel[("Marina District", "Embarcadero")]         = 14
# From Bayview
travel[("Bayview", "Marina District")]           = 27
travel[("Bayview", "Sunset District")]             = 23
travel[("Bayview", "Richmond District")]           = 25
travel[("Bayview", "Nob Hill")]                    = 20
travel[("Bayview", "Chinatown")]                   = 19
travel[("Bayview", "Haight-Ashbury")]              = 19
travel[("Bayview", "North Beach")]                 = 22
travel[("Bayview", "Russian Hill")]                = 23
travel[("Bayview", "Embarcadero")]                 = 19
# From Sunset District
travel[("Sunset District", "Marina District")]     = 21
travel[("Sunset District", "Bayview")]             = 22
travel[("Sunset District", "Richmond District")]   = 12
travel[("Sunset District", "Nob Hill")]            = 27
travel[("Sunset District", "Chinatown")]           = 30
travel[("Sunset District", "Haight-Ashbury")]      = 15
travel[("Sunset District", "North Beach")]         = 28
travel[("Sunset District", "Russian Hill")]        = 24
travel[("Sunset District", "Embarcadero")]           = 30
# From Richmond District
travel[("Richmond District", "Marina District")]   = 9
travel[("Richmond District", "Bayview")]           = 27
travel[("Richmond District", "Sunset District")]     = 11
travel[("Richmond District", "Nob Hill")]            = 17
travel[("Richmond District", "Chinatown")]           = 20
travel[("Richmond District", "Haight-Ashbury")]      = 10
travel[("Richmond District", "North Beach")]         = 17
travel[("Richmond District", "Russian Hill")]        = 13
travel[("Richmond District", "Embarcadero")]           = 19
# From Nob Hill
travel[("Nob Hill", "Marina District")]            = 11
travel[("Nob Hill", "Bayview")]                     = 19
travel[("Nob Hill", "Sunset District")]             = 24
travel[("Nob Hill", "Richmond District")]           = 14
travel[("Nob Hill", "Chinatown")]                   = 6
travel[("Nob Hill", "Haight-Ashbury")]              = 13
travel[("Nob Hill", "North Beach")]                 = 8
travel[("Nob Hill", "Russian Hill")]                = 5
travel[("Nob Hill", "Embarcadero")]                 = 9
# From Chinatown
travel[("Chinatown", "Marina District")]           = 12
travel[("Chinatown", "Bayview")]                    = 20
travel[("Chinatown", "Sunset District")]            = 29
travel[("Chinatown", "Richmond District")]          = 20
travel[("Chinatown", "Nob Hill")]                   = 9
travel[("Chinatown", "Haight-Ashbury")]             = 19
travel[("Chinatown", "North Beach")]                = 3
travel[("Chinatown", "Russian Hill")]               = 7
travel[("Chinatown", "Embarcadero")]                = 5
# From Haight-Ashbury
travel[("Haight-Ashbury", "Marina District")]       = 17
travel[("Haight-Ashbury", "Bayview")]               = 18
travel[("Haight-Ashbury", "Sunset District")]         = 15
travel[("Haight-Ashbury", "Richmond District")]       = 10
travel[("Haight-Ashbury", "Nob Hill")]              = 15
travel[("Haight-Ashbury", "Chinatown")]             = 19
travel[("Haight-Ashbury", "North Beach")]            = 19
travel[("Haight-Ashbury", "Russian Hill")]           = 17
travel[("Haight-Ashbury", "Embarcadero")]            = 20
# From North Beach
travel[("North Beach", "Marina District")]         = 9
travel[("North Beach", "Bayview")]                  = 25
travel[("North Beach", "Sunset District")]          = 27
travel[("North Beach", "Richmond District")]         = 18
travel[("North Beach", "Nob Hill")]                 = 7
travel[("North Beach", "Chinatown")]                = 6
travel[("North Beach", "Haight-Ashbury")]           = 18
travel[("North Beach", "Russian Hill")]             = 4
travel[("North Beach", "Embarcadero")]              = 6
# From Russian Hill
travel[("Russian Hill", "Marina District")]         = 7
travel[("Russian Hill", "Bayview")]                 = 23
travel[("Russian Hill", "Sunset District")]         = 23
travel[("Russian Hill", "Richmond District")]       = 14
travel[("Russian Hill", "Nob Hill")]                = 5
travel[("Russian Hill", "Chinatown")]               = 9
travel[("Russian Hill", "Haight-Ashbury")]          = 17
travel[("Russian Hill", "North Beach")]             = 5
travel[("Russian Hill", "Embarcadero")]             = 8
# From Embarcadero
travel[("Embarcadero", "Marina District")]          = 12
travel[("Embarcadero", "Bayview")]                  = 21
travel[("Embarcadero", "Sunset District")]          = 30
travel[("Embarcadero", "Richmond District")]        = 21
travel[("Embarcadero", "Nob Hill")]                 = 10
travel[("Embarcadero", "Chinatown")]                = 7
travel[("Embarcadero", "Haight-Ashbury")]           = 21
travel[("Embarcadero", "North Beach")]              = 5
travel[("Embarcadero", "Russian Hill")]             = 8

# Set up the Z3 optimization problem.
# We want to choose a subset of friends (and an ordering for the meetings)
# such that all meeting time windows (plus travel time) are respected and
# we maximize the number of meetings scheduled.
opt = Optimize()

# Create a Z3 integer variable for the meeting start time (T)
# and an integer variable for the order in which the meeting occurs.
# order = 0 means the friend is not scheduled.
T_vars    = {}  # meeting start time for each friend (in minutes)
order_vars = {}  # order of meeting (if >0 then scheduled)
for name, info in friend_info.items():
    T_vars[name]    = Int("T_" + name)
    order_vars[name] = Int("order_" + name)
    # order is between 0 and number_of_friends.
    opt.add(order_vars[name] >= 0, order_vars[name] <= len(friend_info))
    # If scheduled then the meeting must occur within the friend’s available window.
    opt.add(Implies(order_vars[name] > 0, T_vars[name] >= info["avail_start"]))
    opt.add(Implies(order_vars[name] > 0, T_vars[name] <= info["avail_end"] - info["duration"]))

# For any friend scheduled as the first meeting (order == 1),
# the meeting start time must allow travel from Marina District.
for name, info in friend_info.items():
    travel_time = travel[("Marina District", info["district"])]
    opt.add(Implies(order_vars[name] == 1, 540 + travel_time <= T_vars[name]))
    
# Ensure that any two scheduled meetings (order > 0) get a unique order.
names = list(friend_info.keys())
for i in range(len(names)):
    for j in range(i+1, len(names)):
        opt.add(Implies(And(order_vars[names[i]] > 0, order_vars[names[j]] > 0),
                         order_vars[names[i]] != order_vars[names[j]]))

# Add constraints to enforce that if friend f is scheduled
# before friend g then the travel time from f's district to g's district,
# plus f’s meeting duration, fits before g’s meeting start time.
for i in range(len(names)):
    for j in range(len(names)):
        if i == j:
            continue
        f = names[i]
        g = names[j]
        travel_time_fg = travel[(friend_info[f]["district"], friend_info[g]["district"])]
        opt.add(Implies(And(order_vars[f] > 0, order_vars[g] > 0, order_vars[f] < order_vars[g]),
                        T_vars[f] + friend_info[f]["duration"] + travel_time_fg <= T_vars[g]))

# Objective: maximize the total number of friends met.
num_scheduled = sum([If(order_vars[name] > 0, 1, 0) for name in names])
opt.maximize(num_scheduled)

# Solve the optimization problem.
if opt.check() == sat:
    model = opt.model()
    scheduled = []
    for name in names:
        if model.evaluate(order_vars[name]).as_long() > 0:
            scheduled.append( (model.evaluate(order_vars[name]).as_long(), 
                               name, 
                               model.evaluate(T_vars[name]).as_long(),
                               friend_info[name]["duration"]) )
    # Sort the scheduled meetings by the order in which they occur.
    scheduled.sort(key=lambda x: x[0])
    
    itinerary = []
    for order_val, name, start, dur in scheduled:
        itinerary.append({
            "action": "meet",
            "person": name,
            "start_time": minutes_to_time(start),
            "end_time": minutes_to_time(start + dur)
        })
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=4))
else:
    print("No solution found")