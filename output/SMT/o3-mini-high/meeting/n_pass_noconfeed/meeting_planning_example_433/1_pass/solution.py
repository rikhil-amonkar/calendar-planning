from z3 import *
import json

def minutes_to_time_str(m):
    # Convert minutes (since 9:00) to 24-hour format (no leading zero for hour)
    total = 9 * 60 + m  # 9:00 is our reference
    hour = total // 60
    minute = total % 60
    return f"{hour}:{minute:02d}"

# Data for each friend: name, meeting location, availability window (in minutes from 9:00),
# required meeting duration, and travel time needed from Nob Hill if visited first.
friends = [
    {"name": "Emily", "location": "Richmond District", "avail_start": 600, "avail_end": 720, "duration": 15, "travel_from_nobhill": 14},
    {"name": "Margaret", "location": "Financial District", "avail_start": 450, "avail_end": 675, "duration": 75, "travel_from_nobhill": 9},
    {"name": "Ronald", "location": "North Beach", "avail_start": 570, "avail_end": 630, "duration": 45, "travel_from_nobhill": 8},
    {"name": "Deborah", "location": "The Castro", "avail_start": 285, "avail_end": 735, "duration": 90, "travel_from_nobhill": 17},
    {"name": "Jeffrey", "location": "Golden Gate Park", "avail_start": 135, "avail_end": 330, "duration": 120, "travel_from_nobhill": 17}
]

# Travel times in minutes between locations.
# Note: The travel times are not necessarily symmetric.
travel_times = {
    "Nob Hill": {
        "Richmond District": 14,
        "Financial District": 9,
        "North Beach": 8,
        "The Castro": 17,
        "Golden Gate Park": 17
    },
    "Richmond District": {
        "Nob Hill": 17,
        "Financial District": 22,
        "North Beach": 17,
        "The Castro": 16,
        "Golden Gate Park": 9
    },
    "Financial District": {
        "Nob Hill": 8,
        "Richmond District": 21,
        "North Beach": 7,
        "The Castro": 23,
        "Golden Gate Park": 23
    },
    "North Beach": {
        "Nob Hill": 7,
        "Richmond District": 18,
        "Financial District": 8,
        "The Castro": 22,
        "Golden Gate Park": 22
    },
    "The Castro": {
        "Nob Hill": 16,
        "Richmond District": 16,
        "Financial District": 20,
        "North Beach": 20,
        "Golden Gate Park": 11
    },
    "Golden Gate Park": {
        "Nob Hill": 20,
        "Richmond District": 7,
        "Financial District": 26,
        "North Beach": 24,
        "The Castro": 13
    }
}

n = len(friends)
opt = Optimize()

# For each friend i, we create two decision variables:
# S[i]: the meeting start time in minutes (from 9:00).
# order_vars[i]: an integer representing the meeting's position in a route.
#   A value of 0 means the meeting is not scheduled; a positive value indicates it is scheduled,
#   with 1 meaning the first meeting visited.
S = [Int(f"S_{i}") for i in range(n)]
order_vars = [Int(f"order_{i}") for i in range(n)]

# Add domain constraints and individual time-window constraints.
for i in range(n):
    friend = friends[i]
    # S[i] must be non-negative.
    opt.add(S[i] >= 0)
    # order_vars[i] is in {0, 1, ..., n}. (0 means not scheduled)
    opt.add(order_vars[i] >= 0, order_vars[i] <= n)
    # If the meeting is scheduled (order > 0) then it must occur within the friend's availability.
    opt.add(Implies(order_vars[i] > 0, S[i] >= friend["avail_start"]))
    opt.add(Implies(order_vars[i] > 0, S[i] + friend["duration"] <= friend["avail_end"]))
    # If the meeting is the first one visited (order == 1) then the meeting start must be at least
    # the travel time from Nob Hill to that friend's location.
    travel_from_start = travel_times["Nob Hill"][friend["location"]]
    opt.add(Implies(order_vars[i] == 1, S[i] >= travel_from_start))

# Enforce that scheduled meetings have distinct order numbers.
for i in range(n):
    for j in range(i + 1, n):
        opt.add(Implies(And(order_vars[i] > 0, order_vars[j] > 0), order_vars[i] != order_vars[j]))

# Chain constraints:
# For every scheduled meeting with order > 1, there must be a scheduled meeting that immediately precedes it
# (i.e. with order equal to its order - 1) such that the travel time from that meeting's location to the current
# meeting's location is accounted for.
for i in range(n):
    friend_i = friends[i]
    # If meeting i is scheduled and is not the first meeting then:
    # There exists some meeting j (j != i) such that order_vars[j] == order_vars[i] - 1 and
    # S[i] >= S[j] + (duration of friend j) + travel time from friend j's location to friend i's location.
    conds = []
    for j in range(n):
        if j == i:
            continue
        friend_j = friends[j]
        cond = And(order_vars[j] == order_vars[i] - 1,
                   S[i] >= S[j] + friend_j["duration"] + travel_times[friend_j["location"]][friend_i["location"]])
        conds.append(cond)
    # If order_vars[i] > 1 then at least one such j must exist.
    opt.add(Implies(order_vars[i] > 1, Or(conds)))

# Objective: maximize the number of scheduled meetings.
num_meetings = Sum([If(order_vars[i] > 0, 1, 0) for i in range(n)])
opt.maximize(num_meetings)

# Check for a solution.
if opt.check() == sat:
    m = opt.model()
    scheduled = []
    for i in range(n):
        ord_val = m.evaluate(order_vars[i]).as_long()
        if ord_val > 0:
            start_val = m.evaluate(S[i]).as_long()
            scheduled.append((ord_val, i, start_val))
    # Sort scheduled meetings by their order in the itinerary.
    scheduled.sort(key=lambda x: x[0])
    
    itinerary = []
    for ord_val, i, start_val in scheduled:
        friend = friends[i]
        start_time_str = minutes_to_time_str(start_val)
        end_time_str = minutes_to_time_str(start_val + friend["duration"])
        itinerary.append({
            "action": "meet",
            "location": friend["location"],
            "person": friend["name"],
            "start_time": start_time_str,
            "end_time": end_time_str
        })
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    # If no feasible itinerary is found, output an empty itinerary.
    print(json.dumps({"itinerary": []}))