from z3 import *
import json

# We measure times in minutes after midnight.
# For example, 9:00AM = 540, 8:15AM = 495, etc.

# Friends’ data: name, location, availability window, and minimum meeting duration.
friends_data = [
    {"name": "Mark",      "location": "Fisherman's Wharf", "avail_start": 495,  "avail_end": 600,  "duration": 30},
    {"name": "Stephanie", "location": "Presidio",          "avail_start": 735,  "avail_end": 900,  "duration": 75},
    {"name": "Betty",     "location": "Bayview",           "avail_start": 435,  "avail_end": 1230, "duration": 15},
    {"name": "Lisa",      "location": "Haight-Ashbury",    "avail_start": 930,  "avail_end": 1110, "duration": 45},
    {"name": "William",   "location": "Russian Hill",      "avail_start": 1125, "avail_end": 1200, "duration": 60},
    {"name": "Brian",     "location": "The Castro",        "avail_start": 555,  "avail_end": 795,  "duration": 30},
    {"name": "Joseph",    "location": "Marina District",   "avail_start": 645,  "avail_end": 900,  "duration": 90},
    {"name": "Ashley",    "location": "Richmond District", "avail_start": 585,  "avail_end": 675,  "duration": 45},
    {"name": "Patricia",  "location": "Union Square",      "avail_start": 990,  "avail_end": 1200, "duration": 120},
    {"name": "Karen",     "location": "Sunset District",   "avail_start": 990,  "avail_end": 1320, "duration": 105},
]

# Starting at the Financial District at 9:00 AM.
start_location = "Financial District"
start_time = 540  # 9:00 AM in minutes

# Travel times (in minutes) from one district to another, as provided.
# (Note: The times are not strictly symmetric.)
travel = {}

# From Financial District:
travel[("Financial District", "Fisherman's Wharf")] = 10
travel[("Financial District", "Presidio")]            = 22
travel[("Financial District", "Bayview")]             = 19
travel[("Financial District", "Haight-Ashbury")]        = 19
travel[("Financial District", "Russian Hill")]          = 11
travel[("Financial District", "The Castro")]            = 20
travel[("Financial District", "Marina District")]       = 15
travel[("Financial District", "Richmond District")]     = 21
travel[("Financial District", "Union Square")]          = 9
travel[("Financial District", "Sunset District")]       = 30

# From Fisherman's Wharf:
travel[("Fisherman's Wharf", "Financial District")] = 11
travel[("Fisherman's Wharf", "Presidio")]           = 17
travel[("Fisherman's Wharf", "Bayview")]            = 26
travel[("Fisherman's Wharf", "Haight-Ashbury")]       = 22
travel[("Fisherman's Wharf", "Russian Hill")]         = 7
travel[("Fisherman's Wharf", "The Castro")]           = 27
travel[("Fisherman's Wharf", "Marina District")]      = 9
travel[("Fisherman's Wharf", "Richmond District")]    = 18
travel[("Fisherman's Wharf", "Union Square")]         = 13
travel[("Fisherman's Wharf", "Sunset District")]      = 27

# From Presidio:
travel[("Presidio", "Financial District")]       = 23
travel[("Presidio", "Fisherman's Wharf")]          = 19
travel[("Presidio", "Bayview")]                   = 31
travel[("Presidio", "Haight-Ashbury")]              = 15
travel[("Presidio", "Russian Hill")]                = 14
travel[("Presidio", "The Castro")]                  = 21
travel[("Presidio", "Marina District")]             = 11
travel[("Presidio", "Richmond District")]           = 7
travel[("Presidio", "Union Square")]                = 22
travel[("Presidio", "Sunset District")]             = 15

# From Bayview:
travel[("Bayview", "Financial District")]         = 19
travel[("Bayview", "Fisherman's Wharf")]            = 25
travel[("Bayview", "Presidio")]                     = 32
travel[("Bayview", "Haight-Ashbury")]               = 19
travel[("Bayview", "Russian Hill")]                 = 23
travel[("Bayview", "The Castro")]                   = 19
travel[("Bayview", "Marina District")]              = 27
travel[("Bayview", "Richmond District")]            = 25
travel[("Bayview", "Union Square")]                 = 18
travel[("Bayview", "Sunset District")]              = 23

# From Haight-Ashbury:
travel[("Haight-Ashbury", "Financial District")]    = 21
travel[("Haight-Ashbury", "Fisherman's Wharf")]       = 23
travel[("Haight-Ashbury", "Presidio")]                = 15
travel[("Haight-Ashbury", "Bayview")]                 = 18
travel[("Haight-Ashbury", "Russian Hill")]            = 17
travel[("Haight-Ashbury", "The Castro")]              = 6
travel[("Haight-Ashbury", "Marina District")]         = 17
travel[("Haight-Ashbury", "Richmond District")]       = 10
travel[("Haight-Ashbury", "Union Square")]            = 19
travel[("Haight-Ashbury", "Sunset District")]         = 15

# From Russian Hill:
travel[("Russian Hill", "Financial District")]      = 11
travel[("Russian Hill", "Fisherman's Wharf")]         = 7
travel[("Russian Hill", "Presidio")]                  = 14
travel[("Russian Hill", "Bayview")]                   = 23
travel[("Russian Hill", "Haight-Ashbury")]            = 17
travel[("Russian Hill", "The Castro")]                = 21
travel[("Russian Hill", "Marina District")]           = 7
travel[("Russian Hill", "Richmond District")]         = 14
travel[("Russian Hill", "Union Square")]              = 10
travel[("Russian Hill", "Sunset District")]           = 23

# From The Castro:
travel[("The Castro", "Financial District")]        = 21
travel[("The Castro", "Fisherman's Wharf")]           = 24
travel[("The Castro", "Presidio")]                    = 20
travel[("The Castro", "Bayview")]                     = 19
travel[("The Castro", "Haight-Ashbury")]              = 6
travel[("The Castro", "Russian Hill")]                = 18
travel[("The Castro", "Marina District")]             = 21
travel[("The Castro", "Richmond District")]           = 16
travel[("The Castro", "Union Square")]                = 19
travel[("The Castro", "Sunset District")]             = 17

# From Marina District:
travel[("Marina District", "Financial District")]   = 17
travel[("Marina District", "Fisherman's Wharf")]      = 10
travel[("Marina District", "Presidio")]               = 10
travel[("Marina District", "Bayview")]                = 27
travel[("Marina District", "Haight-Ashbury")]         = 16
travel[("Marina District", "Russian Hill")]           = 8
travel[("Marina District", "The Castro")]             = 22
travel[("Marina District", "Richmond District")]      = 11
travel[("Marina District", "Union Square")]           = 16
travel[("Marina District", "Sunset District")]        = 19

# From Richmond District:
travel[("Richmond District", "Financial District")] = 22
travel[("Richmond District", "Fisherman's Wharf")]    = 18
travel[("Richmond District", "Presidio")]             = 7
travel[("Richmond District", "Bayview")]              = 27
travel[("Richmond District", "Haight-Ashbury")]       = 10
travel[("Richmond District", "Russian Hill")]         = 14
travel[("Richmond District", "The Castro")]           = 16
travel[("Richmond District", "Marina District")]      = 9
travel[("Richmond District", "Union Square")]         = 21
travel[("Richmond District", "Sunset District")]      = 11

# From Union Square:
travel[("Union Square", "Financial District")]      = 9
travel[("Union Square", "Fisherman's Wharf")]         = 15
travel[("Union Square", "Presidio")]                  = 24
travel[("Union Square", "Bayview")]                   = 15
travel[("Union Square", "Haight-Ashbury")]            = 18
travel[("Union Square", "Russian Hill")]              = 13
travel[("Union Square", "The Castro")]                = 17
travel[("Union Square", "Marina District")]           = 18
travel[("Union Square", "Richmond District")]         = 20
travel[("Union Square", "Sunset District")]           = 27

# From Sunset District:
travel[("Sunset District", "Financial District")]   = 30
travel[("Sunset District", "Fisherman's Wharf")]      = 29
travel[("Sunset District", "Presidio")]               = 16
travel[("Sunset District", "Bayview")]                = 22
travel[("Sunset District", "Haight-Ashbury")]         = 15
travel[("Sunset District", "Russian Hill")]           = 24
travel[("Sunset District", "The Castro")]             = 17
travel[("Sunset District", "Marina District")]        = 21
travel[("Sunset District", "Richmond District")]      = 12
travel[("Sunset District", "Union Square")]           = 30

# Create an Optimize solver.
opt = Optimize()

# For each friend, create a Boolean variable indicating whether we schedule a meeting,
# and an Int variable for the meeting’s start time.
scheduled = {}
start_vars = {}

for f in friends_data:
    name = f["name"]
    scheduled[name] = Bool("sched_" + name)
    start_vars[name] = Int("start_" + name)
    # If scheduled, the meeting must start no earlier than the friend’s available time,
    # and finish (start + duration) by the available end.
    opt.add(Or(Not(scheduled[name]),
               And(start_vars[name] >= f["avail_start"],
                   start_vars[name] <= f["avail_end"] - f["duration"])))
    # Also, if scheduled, you must travel from your start location (Financial District) to the meeting’s location.
    if f["location"] != start_location:
        if (start_location, f["location"]) in travel:
            opt.add(Or(Not(scheduled[name]),
                       start_vars[name] >= start_time + travel[(start_location, f["location"])]))
        else:
            opt.add(Or(Not(scheduled[name]),
                       start_vars[name] >= start_time))
    else:
        opt.add(Or(Not(scheduled[name]),
                   start_vars[name] >= start_time))

# For every two meetings that are both scheduled, force a non‐overlap
# that accounts for each meeting’s duration plus the travel time in between.
names = [f["name"] for f in friends_data]
for i in range(len(names)):
    for j in range(i+1, len(names)):
        n1 = names[i]
        n2 = names[j]
        # Get meeting durations:
        dur1 = next(item["duration"] for item in friends_data if item["name"] == n1)
        dur2 = next(item["duration"] for item in friends_data if item["name"] == n2)
        # Get locations:
        loc1 = next(item["location"] for item in friends_data if item["name"] == n1)
        loc2 = next(item["location"] for item in friends_data if item["name"] == n2)
        # Travel times between the two locations:
        t_12 = travel[(loc1, loc2)] if (loc1, loc2) in travel else 0
        t_21 = travel[(loc2, loc1)] if (loc2, loc1) in travel else 0
        opt.add(Implies(And(scheduled[n1], scheduled[n2]),
                        Or(start_vars[n1] + dur1 + t_12 <= start_vars[n2],
                           start_vars[n2] + dur2 + t_21 <= start_vars[n1])))

# Our objective is to meet as many friends as possible.
opt.maximize(Sum([If(scheduled[name], 1, 0) for name in names]))

# Solve.
if opt.check() == sat:
    model = opt.model()
    # Build the itinerary: only include scheduled meetings.
    # For each meeting, the end time is start time + duration.
    itinerary = []
    for f in friends_data:
        name = f["name"]
        if model.evaluate(scheduled[name]):
            start_val = model.evaluate(start_vars[name]).as_long()
            end_val = start_val + f["duration"]
            # Format times in HH:MM (24-hour format).
            itinerary.append((start_val, {
                "action": "meet",
                "person": name,
                "start_time": f"{start_val // 60:02d}:{start_val % 60:02d}",
                "end_time": f"{end_val // 60:02d}:{end_val % 60:02d}"
            }))
    # Sort the meetings by start time.
    itinerary.sort(key=lambda x: x[0])
    itinerary = [item[1] for item in itinerary]
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    print("No solution found")