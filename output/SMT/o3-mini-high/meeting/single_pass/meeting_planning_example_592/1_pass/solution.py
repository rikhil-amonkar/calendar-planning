from z3 import Int, Optimize, Implies, Distinct, sat
import json

# Helper function: converts minutes since midnight to "HH:MM" string.
def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

# Define the information for each friend.
# Times are in minutes from midnight.
# 9:00 AM is 540, 9:30 AM is 570, 15:30 is 930, etc.
friends = [
    {"name": "James",   "location": "Pacific Heights", "avail_start": 1200, "avail_end": 1320, "min_duration": 120},  # 20:00-22:00
    {"name": "Robert",  "location": "Chinatown",       "avail_start": 735,  "avail_end": 1005, "min_duration": 90},   # 12:15-16:45
    {"name": "Jeffrey", "location": "Union Square",    "avail_start": 570,  "avail_end": 930,  "min_duration": 120},  # 09:30-15:30
    {"name": "Carol",   "location": "Mission District","avail_start": 1095, "avail_end": 1275, "min_duration": 15},   # 18:15-21:15
    {"name": "Mark",    "location": "Golden Gate Park","avail_start": 690,  "avail_end": 1065, "min_duration": 15},   # 11:30-17:45
    {"name": "Sandra",  "location": "Nob Hill",        "avail_start": 480,  "avail_end": 930,  "min_duration": 15},   # 08:00-15:30
]

n = len(friends)

# Travel time matrix (in minutes) as provided.
travel = {
    ("North Beach", "Pacific Heights"): 8,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Mission District"): 18,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Nob Hill"): 7,
    ("Pacific Heights", "North Beach"): 9,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Chinatown", "North Beach"): 3,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Mission District"): 18,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Nob Hill"): 8,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Mission District"): 14,
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Nob Hill"): 9,
    ("Mission District", "North Beach"): 17,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Chinatown"): 16,
    ("Mission District", "Union Square"): 15,
    ("Mission District", "Golden Gate Park"): 17,
    ("Mission District", "Nob Hill"): 12,
    ("Golden Gate Park", "North Beach"): 24,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Mission District"): 17,
    ("Golden Gate Park", "Nob Hill"): 20,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "Mission District"): 13,
    ("Nob Hill", "Golden Gate Park"): 17,
}

def get_travel_time(from_loc, to_loc):
    # Lookup the travel time between two locations.
    # We assume the pair is always found.
    return travel[(from_loc, to_loc)]

# Create an Optimize instance.
opt = Optimize()

# For each friend we create integer variables for the meeting start time, end time, and order position.
# Times are in minutes since midnight.
start_vars = [Int(f"start_{i}") for i in range(n)]
end_vars   = [Int(f"end_{i}") for i in range(n)]
order_vars = [Int(f"order_{i}") for i in range(n)]
# In this formulation we assume we are meeting all friends.

# Add constraints for each friend regarding time availability and minimum meeting duration.
for i in range(n):
    f = friends[i]
    # Meeting must occur within the friend’s availability window.
    opt.add(start_vars[i] >= f["avail_start"])
    opt.add(end_vars[i]   <= f["avail_end"])
    # Meeting must last at least the required minimum duration.
    opt.add(end_vars[i] - start_vars[i] >= f["min_duration"])
    # Order variables: if a friend is scheduled, its order is between 1 and n.
    opt.add(order_vars[i] >= 1, order_vars[i] <= n)

# All order values must be distinct (i.e. a strict sequence).
opt.add(Distinct(order_vars))

# The first meeting in the schedule must be reachable from North Beach.
arrival_time = 540  # 9:00 AM in minutes
for i in range(n):
    tt = get_travel_time("North Beach", friends[i]["location"])
    opt.add(Implies(order_vars[i] == 1, start_vars[i] >= arrival_time + tt))

# For any two meetings i and j, if i comes before j then account for travel time between their locations.
for i in range(n):
    for j in range(n):
        if i != j:
            tt = get_travel_time(friends[i]["location"], friends[j]["location"])
            opt.add(Implies(order_vars[i] < order_vars[j],
                            start_vars[j] >= end_vars[i] + tt))

# (Optional) Objective: maximize the total number of meetings.
# Since we assume all meetings are scheduled, this is simply n.
total_meetings = n
opt.maximize(total_meetings)

# Check for a solution.
if opt.check() == sat:
    model = opt.model()
    # Collect and sort meetings by their order (i.e. their position in the sequence).
    meeting_list = []
    order_list = []
    for i in range(n):
        order_val = model[order_vars[i]].as_long()
        order_list.append((order_val, i))
    order_list.sort()  # sort by order value
    for order_val, i in order_list:
        s = model[start_vars[i]].as_long()
        e = model[end_vars[i]].as_long()
        meeting_list.append({
            "action": "meet",
            "person": friends[i]["name"],
            "start_time": minutes_to_time(s),
            "end_time": minutes_to_time(e)
        })
    itinerary = {"itinerary": meeting_list}
    print(json.dumps(itinerary, indent=2))
else:
    print("No solution found")