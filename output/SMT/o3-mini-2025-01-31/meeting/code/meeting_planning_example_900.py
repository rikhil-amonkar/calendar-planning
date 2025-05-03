from z3 import *

# ---------------------------
# Data definitions
# ---------------------------
# Define friend meeting data. We convert times to minutes after 9:00 AM.
# Times: 9:00AM = 0.
# For example, 11:15AM -> 135 (because 9:00 -> 11:15 is 2h15 = 135 minutes)
friends = [
    {"name": "Matthew", "location": "The Castro", "avail_start": 450, "avail_end": 660, "duration": 45},    # 4:30PM to 8:00PM
    {"name": "Rebecca", "location": "Nob Hill", "avail_start": 375, "avail_end": 615, "duration": 105},       # 3:15PM to 7:15PM
    {"name": "Brian", "location": "Marina District", "avail_start": 315, "avail_end": 780, "duration": 30},   # 2:15PM to 10:00PM
    {"name": "Emily", "location": "Pacific Heights", "avail_start": 135, "avail_end": 645, "duration": 15},   # 11:15AM to 7:45PM
    {"name": "Karen", "location": "Haight-Ashbury", "avail_start": 165, "avail_end": 510, "duration": 30},      # 11:45AM to 5:30PM
    {"name": "Stephanie", "location": "Mission District", "avail_start": 240, "avail_end": 405, "duration": 75},# 1:00PM to 3:45PM
    {"name": "James", "location": "Chinatown", "avail_start": 330, "avail_end": 600, "duration": 120},          # 2:30PM to 7:00PM
    {"name": "Steven", "location": "Russian Hill", "avail_start": 300, "avail_end": 660, "duration": 30},       # 2:00PM to 8:00PM
    {"name": "Elizabeth", "location": "Alamo Square", "avail_start": 240, "avail_end": 375, "duration": 120},   # 1:00PM to 5:15PM
    {"name": "William", "location": "Bayview", "avail_start": 555, "avail_end": 615, "duration": 90}            # 6:15PM to 8:15PM
]

# List of all locations (include starting location "Richmond District")
locations = ["Richmond District", "The Castro", "Nob Hill", "Marina District", "Pacific Heights",
             "Haight-Ashbury", "Mission District", "Chinatown", "Russian Hill", "Alamo Square", "Bayview"]

# Travel times in minutes.
# We create a dictionary keyed by (origin, destination)
travel = {
    ("Richmond District","The Castro"): 16,
    ("Richmond District","Nob Hill"): 17,
    ("Richmond District","Marina District"): 9,
    ("Richmond District","Pacific Heights"): 10,
    ("Richmond District","Haight-Ashbury"): 10,
    ("Richmond District","Mission District"): 20,
    ("Richmond District","Chinatown"): 20,
    ("Richmond District","Russian Hill"): 13,
    ("Richmond District","Alamo Square"): 13,
    ("Richmond District","Bayview"): 27,

    ("The Castro","Richmond District"): 16,
    ("The Castro","Nob Hill"): 16,
    ("The Castro","Marina District"): 21,
    ("The Castro","Pacific Heights"): 16,
    ("The Castro","Haight-Ashbury"): 6,
    ("The Castro","Mission District"): 7,
    ("The Castro","Chinatown"): 22,
    ("The Castro","Russian Hill"): 18,
    ("The Castro","Alamo Square"): 8,
    ("The Castro","Bayview"): 19,

    ("Nob Hill","Richmond District"): 14,
    ("Nob Hill","The Castro"): 17,
    ("Nob Hill","Marina District"): 11,
    ("Nob Hill","Pacific Heights"): 8,
    ("Nob Hill","Haight-Ashbury"): 13,
    ("Nob Hill","Mission District"): 13,
    ("Nob Hill","Chinatown"): 6,
    ("Nob Hill","Russian Hill"): 5,
    ("Nob Hill","Alamo Square"): 11,
    ("Nob Hill","Bayview"): 19,

    ("Marina District","Richmond District"): 11,
    ("Marina District","The Castro"): 22,
    ("Marina District","Nob Hill"): 12,
    ("Marina District","Pacific Heights"): 7,
    ("Marina District","Haight-Ashbury"): 16,
    ("Marina District","Mission District"): 20,
    ("Marina District","Chinatown"): 15,
    ("Marina District","Russian Hill"): 8,
    ("Marina District","Alamo Square"): 15,
    ("Marina District","Bayview"): 27,

    ("Pacific Heights","Richmond District"): 12,
    ("Pacific Heights","The Castro"): 16,
    ("Pacific Heights","Nob Hill"): 8,
    ("Pacific Heights","Marina District"): 6,
    ("Pacific Heights","Haight-Ashbury"): 11,
    ("Pacific Heights","Mission District"): 15,
    ("Pacific Heights","Chinatown"): 11,
    ("Pacific Heights","Russian Hill"): 7,
    ("Pacific Heights","Alamo Square"): 10,
    ("Pacific Heights","Bayview"): 22,

    ("Haight-Ashbury","Richmond District"): 10,
    ("Haight-Ashbury","The Castro"): 6,
    ("Haight-Ashbury","Nob Hill"): 15,
    ("Haight-Ashbury","Marina District"): 17,
    ("Haight-Ashbury","Pacific Heights"): 12,
    ("Haight-Ashbury","Mission District"): 11,
    ("Haight-Ashbury","Chinatown"): 19,
    ("Haight-Ashbury","Russian Hill"): 17,
    ("Haight-Ashbury","Alamo Square"): 5,
    ("Haight-Ashbury","Bayview"): 18,

    ("Mission District","Richmond District"): 20,
    ("Mission District","The Castro"): 7,
    ("Mission District","Nob Hill"): 12,
    ("Mission District","Marina District"): 19,
    ("Mission District","Pacific Heights"): 16,
    ("Mission District","Haight-Ashbury"): 12,
    ("Mission District","Chinatown"): 16,
    ("Mission District","Russian Hill"): 15,
    ("Mission District","Alamo Square"): 11,
    ("Mission District","Bayview"): 14,

    ("Chinatown","Richmond District"): 20,
    ("Chinatown","The Castro"): 22,
    ("Chinatown","Nob Hill"): 9,
    ("Chinatown","Marina District"): 12,
    ("Chinatown","Pacific Heights"): 10,
    ("Chinatown","Haight-Ashbury"): 19,
    ("Chinatown","Mission District"): 17,
    ("Chinatown","Russian Hill"): 7,
    ("Chinatown","Alamo Square"): 17,
    ("Chinatown","Bayview"): 20,

    ("Russian Hill","Richmond District"): 14,
    ("Russian Hill","The Castro"): 21,
    ("Russian Hill","Nob Hill"): 5,
    ("Russian Hill","Marina District"): 7,
    ("Russian Hill","Pacific Heights"): 7,
    ("Russian Hill","Haight-Ashbury"): 17,
    ("Russian Hill","Mission District"): 16,
    ("Russian Hill","Chinatown"): 9,
    ("Russian Hill","Alamo Square"): 15,
    ("Russian Hill","Bayview"): 23,

    ("Alamo Square","Richmond District"): 11,
    ("Alamo Square","The Castro"): 8,
    ("Alamo Square","Nob Hill"): 11,
    ("Alamo Square","Marina District"): 15,
    ("Alamo Square","Pacific Heights"): 10,
    ("Alamo Square","Haight-Ashbury"): 5,
    ("Alamo Square","Mission District"): 10,
    ("Alamo Square","Chinatown"): 15,
    ("Alamo Square","Russian Hill"): 13,
    ("Alamo Square","Bayview"): 16,

    ("Bayview","Richmond District"): 25,
    ("Bayview","The Castro"): 19,
    ("Bayview","Nob Hill"): 20,
    ("Bayview","Marina District"): 27,
    ("Bayview","Pacific Heights"): 23,
    ("Bayview","Haight-Ashbury"): 19,
    ("Bayview","Mission District"): 13,
    ("Bayview","Chinatown"): 19,
    ("Bayview","Russian Hill"): 23,
    ("Bayview","Alamo Square"): 16,
}

def get_travel_time(orig, dest):
    # We assume the travel time exists between these two locations.
    return travel[(orig, dest)]

# -----------------------------
# Z3 Model
# -----------------------------

# Create an optimizer so we can maximize scheduled meetings.
opt = Optimize()

n = len(friends)

# Decision variables
# For each friend i, x[i] = True if meeting is scheduled, and start[i] is start time (in minutes after 9:00AM)
x = [Bool(f"x_{i}") for i in range(n)]
start = [Int(f"start_{i}") for i in range(n)]
# We also define meeting end time implicitly as: start + duration.

# We will allow meeting start times to be in a reasonable range.
for i in range(n):
    # Constrain start[i] to be nonnegative and less than some large number.
    opt.add(start[i] >= 0, start[i] <= 1000)

# For each friend, if scheduled then:
for i, f in enumerate(friends):
    req = f["duration"]
    availS = f["avail_start"]
    availE = f["avail_end"]
    loc = f["location"]
    # Must respect friend’s time window if meeting occurs:
    opt.add(Implies(x[i], start[i] >= availS))
    opt.add(Implies(x[i], start[i] + req <= availE))
    # Also, you must travel from the Richmond District (starting point) to friend’s location.
    travel_from_richmond = get_travel_time("Richmond District", loc)
    opt.add(Implies(x[i], start[i] >= travel_from_richmond))
    
# Now add non-overlap travel constraints between every pair of meetings if both scheduled.
# For any two distinct meetings i and j, if both are scheduled then we require either:
# meeting i finishes and you can travel from i to j in time for j’s start, OR vice-versa.
for i in range(n):
    for j in range(i+1, n):
        req_i = friends[i]["duration"]
        req_j = friends[j]["duration"]
        loc_i = friends[i]["location"]
        loc_j = friends[j]["location"]
        travel_i_j = get_travel_time(loc_i, loc_j)
        travel_j_i = get_travel_time(loc_j, loc_i)
        # Constraint:
        cond = Or( start[i] + req_i + travel_i_j <= start[j],
                   start[j] + req_j + travel_j_i <= start[i] )
        opt.add(Implies(And(x[i], x[j]), cond))

# In addition, if a meeting is not scheduled then we do not care about its start time.
# (The above constraints are conditional.)

# -----------------------------
# Objective: Maximize number of meetings scheduled.
# -----------------------------
opt.maximize(Sum([If(x[i], 1, 0) for i in range(n)]))

# -----------------------------
# Solve the model
# -----------------------------
if opt.check() == sat:
    m = opt.model()
    scheduled_meetings = []
    for i in range(n):
        if m.evaluate(x[i]):
            st = m.evaluate(start[i]).as_long()
            scheduled_meetings.append((st, friends[i]["name"], friends[i]["location"], friends[i]["duration"]))
    scheduled_meetings.sort(key=lambda t: t[0])
    print("Optimal schedule (times in minutes after 9:00AM):")
    for st, name, loc, dur in scheduled_meetings:
        # Compute finish time
        finish = st + dur
        # Convert minutes to clock time (9:00 AM + minutes)
        def to_time(minutes):
            hour = 9 + minutes // 60
            minute = minutes % 60
            return f"{hour:02d}:{minute:02d}"
        print(f"Meet {name} at {loc}: from {to_time(st)} to {to_time(finish)} (duration {dur} mins)")
else:
    print("No feasible schedule found.")