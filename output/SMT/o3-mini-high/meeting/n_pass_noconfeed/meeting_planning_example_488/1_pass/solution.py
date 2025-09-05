from z3 import Int, If, And, Or, Implies, Optimize, sat
import json

# Helper: convert time string "H:MM" to minutes from midnight
def time_to_minutes(t_str):
    parts = t_str.split(":")
    return int(parts[0]) * 60 + int(parts[1])

# Friend meeting data with availability windows (in minutes from midnight) and required meeting durations (in minutes)
# Ronald: available 10:00 (600) to 17:00 (1020), duration 105
# Sarah: available 7:15 (435) to 9:30 (570), duration 45
# Helen: available 13:30 (810) to 17:00 (1020), duration 120
# Joshua: available 14:15 (855) to 19:30 (1170), duration 90
# Margaret: available 10:15 (615) to 22:00 (1320), duration 60
friends = [
    {"name": "Ronald", "location": "Nob Hill",      "avail_start": 600,  "avail_end": 1020, "duration": 105},
    {"name": "Sarah",   "location": "Russian Hill",  "avail_start": 435,  "avail_end": 570,  "duration": 45},
    {"name": "Helen",   "location": "The Castro",    "avail_start": 810,  "avail_end": 1020, "duration": 120},
    {"name": "Joshua",  "location": "Sunset District","avail_start": 855,  "avail_end": 1170, "duration": 90},
    {"name": "Margaret","location": "Haight-Ashbury","avail_start": 615,  "avail_end": 1320, "duration": 60}
]

# Travel times in minutes between locations (symmetric matrix)
travel = {
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Russian Hill"): 7,
    ("Pacific Heights", "The Castro"): 16,
    ("Pacific Heights", "Sunset District"): 21,
    ("Pacific Heights", "Haight-Ashbury"): 11,
    
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "Russian Hill"): 5,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "Sunset District"): 25,
    ("Nob Hill", "Haight-Ashbury"): 13,
    
    ("Russian Hill", "Pacific Heights"): 7,
    ("Russian Hill", "Nob Hill"): 5,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Haight-Ashbury"): 17,
    
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "Sunset District"): 17,
    ("The Castro", "Haight-Ashbury"): 6,
    
    ("Sunset District", "Pacific Heights"): 21,
    ("Sunset District", "Nob Hill"): 27,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "Haight-Ashbury"): 15,
    
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Haight-Ashbury", "Nob Hill"): 15,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "The Castro"): 6,
    ("Haight-Ashbury", "Sunset District"): 15,
}

# Starting point: You arrive at Pacific Heights at 9:00AM = 540 minutes from midnight.
start_location = "Pacific Heights"
start_time = 540

# Number of friends
n = len(friends)

# Create an Optimize object from Z3
opt = Optimize()

# For each friend, define an integer variable "order" (0 means not scheduled; if >0, it is the meeting order)
order_vars = [Int(f"order_{i}") for i in range(n)]
# For each friend, define an integer variable for the meeting start time (in minutes from midnight)
start_vars = [Int(f"start_{i}") for i in range(n)]

# Add domain constraints: order is between 0 and n, start time is non-negative.
for i in range(n):
    opt.add(order_vars[i] >= 0, order_vars[i] <= n)
    opt.add(start_vars[i] >= 0)

# If a friend is scheduled (order > 0), then the meeting must occur within their availability window 
# and last at least the required duration.
for i, friend in enumerate(friends):
    avail_start = friend["avail_start"]
    avail_end = friend["avail_end"]
    dur = friend["duration"]
    loc = friend["location"]

    # Meeting must start no earlier than the friend's availability start
    opt.add(Implies(order_vars[i] > 0, start_vars[i] >= avail_start))
    # Meeting must end (start + required duration) no later than the friend's availability end.
    opt.add(Implies(order_vars[i] > 0, start_vars[i] + dur <= avail_end))
    # If the meeting is scheduled as the first meeting (order == 1), you must travel from Pacific Heights.
    travel_first = travel[(start_location, loc)]
    opt.add(Implies(order_vars[i] == 1, start_vars[i] >= start_time + travel_first))

# For any two different scheduled meetings, their order numbers must be distinct.
for i in range(n):
    for j in range(i+1, n):
        opt.add(Implies(And(order_vars[i] > 0, order_vars[j] > 0), order_vars[i] != order_vars[j]))

# For any two scheduled meetings, if one is scheduled before the other (by order), then 
# the later meeting can only start after the previous meeting finishes and you travel between locations.
for i in range(n):
    for j in range(n):
        if i != j:
            dur_i = friends[i]["duration"]
            loc_i = friends[i]["location"]
            loc_j = friends[j]["location"]
            travel_time_ij = travel[(loc_i, loc_j)]
            opt.add(Implies(And(order_vars[i] > 0, order_vars[j] > 0, order_vars[i] < order_vars[j]),
                            start_vars[j] >= start_vars[i] + dur_i + travel_time_ij))

# Ensure that if any meeting is scheduled, then there is at least one meeting with order == 1.
# (If no meetings are scheduled, this constraint is inactive.)
opt.add(Implies(Or([order_vars[i] > 0 for i in range(n)]), Or([order_vars[i] == 1 for i in range(n)])))

# Define the objective: maximize the number of scheduled meetings.
count_expr = sum([If(order_vars[i] > 0, 1, 0) for i in range(n)])
h = opt.maximize(count_expr)

# Check for a solution
if opt.check() == sat:
    model = opt.model()
    itinerary = []
    scheduled = []
    # Gather scheduled meetings (order > 0) with their order and start times.
    for i in range(n):
        o_val = model.evaluate(order_vars[i]).as_long()
        if o_val > 0:
            s_val = model.evaluate(start_vars[i]).as_long()
            scheduled.append((o_val, i, s_val))
    # Sort meetings by their scheduled order.
    scheduled.sort(key=lambda x: x[0])
    
    # Helper to format minutes to "H:MM" 24-hour format.
    def format_time(t):
        h = t // 60
        m = t % 60
        return f"{h}:{m:02d}"
    
    # Build the itinerary list.
    for order_val, i, s_val in scheduled:
        friend = friends[i]
        dur = friend["duration"]
        itinerary.append({
            "action": "meet",
            "location": friend["location"],
            "person": friend["name"],
            "start_time": format_time(s_val),
            "end_time": format_time(s_val + dur)
        })
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    print(json.dumps({"itinerary": []}))