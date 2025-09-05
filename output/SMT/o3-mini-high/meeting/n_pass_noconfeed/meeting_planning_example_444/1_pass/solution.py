from z3 import *
import json

def convert_time(minutes_after_9):
    # Convert minutes after 9:00 to a 24-hour time string.
    total = 540 + minutes_after_9  # 9:00 AM is 540 minutes after midnight
    hour = total // 60
    minute = total % 60
    return f"{hour}:{minute:02d}"

# Travel times (in minutes) between locations.
travel_times = {
    ("Financial District", "Russian Hill"): 10,
    ("Financial District", "Sunset District"): 31,
    ("Financial District", "North Beach"): 7,
    ("Financial District", "The Castro"): 23,
    ("Financial District", "Golden Gate Park"): 23,
    
    ("Russian Hill", "Financial District"): 11,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "North Beach"): 5,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Golden Gate Park"): 21,
    
    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "North Beach"): 29,
    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "Golden Gate Park"): 11,
    
    ("North Beach", "Financial District"): 8,
    ("North Beach", "Russian Hill"): 4,
    ("North Beach", "Sunset District"): 27,
    ("North Beach", "The Castro"): 22,
    ("North Beach", "Golden Gate Park"): 22,
    
    ("The Castro", "Financial District"): 20,
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "Sunset District"): 17,
    ("The Castro", "North Beach"): 20,
    ("The Castro", "Golden Gate Park"): 11,
    
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "North Beach"): 24,
    ("Golden Gate Park", "The Castro"): 13,
}

# Define the friends' meeting constraints.
# Times are expressed in minutes after 9:00 AM.
# 9:00 AM is time 0.
friends = [
    {
        "name": "Ronald",
        "location": "Russian Hill",
        "avail_start": 285,  # 13:45 = 285 minutes after 9:00
        "avail_end": 495,    # 17:15 = 495 minutes after 9:00
        "min_dur": 105
    },
    {
        "name": "Patricia",
        "location": "Sunset District",
        "avail_start": 15,   # 9:15 = 15 minutes after 9:00
        "avail_end": 780,    # 22:00 = 780 minutes after 9:00
        "min_dur": 60
    },
    {
        "name": "Laura",
        "location": "North Beach",
        "avail_start": 210,  # 12:30 = 210 minutes after 9:00
        "avail_end": 225,    # 12:45 = 225 minutes after 9:00
        "min_dur": 15
    },
    {
        "name": "Emily",
        "location": "The Castro",
        "avail_start": 435,  # 16:15 = 435 minutes after 9:00
        "avail_end": 570,    # 18:30 = 570 minutes after 9:00
        "min_dur": 60
    },
    {
        "name": "Mary",
        "location": "Golden Gate Park",
        "avail_start": 360,  # 15:00 = 360 minutes after 9:00
        "avail_end": 450,    # 16:30 = 450 minutes after 9:00
        "min_dur": 60
    },
]

n = len(friends)
opt = Optimize()

# Decision variables for each friend:
# scheduled[i]: whether to meet friend i.
# order[i]: the position (1...n) in the sequence if scheduled (0 if not scheduled).
# start[i], end[i]: the start and end times of the meeting (minutes after 9:00).
scheduled = [Bool(f"scheduled_{i}") for i in range(n)]
order_vars = [Int(f"order_{i}") for i in range(n)]
start_vars = [Int(f"start_{i}") for i in range(n)]
end_vars = [Int(f"end_{i}") for i in range(n)]

for i, friend in enumerate(friends):
    avail_start = friend["avail_start"]
    avail_end = friend["avail_end"]
    min_dur = friend["min_dur"]
    # If scheduled, then:
    #   - order is between 1 and n,
    #   - meeting starts no earlier than avail_start,
    #   - meeting ends no later than avail_end,
    #   - meeting duration meets the required minimum.
    opt.add(If(scheduled[i],
               And(order_vars[i] >= 1, order_vars[i] <= n,
                   start_vars[i] >= avail_start,
                   end_vars[i] <= avail_end,
                   end_vars[i] - start_vars[i] >= min_dur),
               order_vars[i] == 0))
    # Ensuring nonnegative start values if scheduled.
    opt.add(If(scheduled[i], start_vars[i] >= 0, True))

# Ensure that if two meetings are scheduled, they occupy different positions.
for i in range(n):
    for j in range(i+1, n):
        opt.add(Implies(And(scheduled[i], scheduled[j]), order_vars[i] != order_vars[j]))

# Add sequencing (travel) constraints.
# For any two scheduled meetings, if meeting i comes before meeting j,
# then meeting j cannot start until after meeting i finishes and travel time is accounted for.
for i in range(n):
    for j in range(n):
        if i != j:
            loc_i = friends[i]["location"]
            loc_j = friends[j]["location"]
            travel = travel_times[(loc_i, loc_j)]
            opt.add(Implies(And(scheduled[i], scheduled[j], order_vars[i] < order_vars[j]),
                            start_vars[j] >= end_vars[i] + travel))

# For the first scheduled meeting, account for travel time from the Financial District (arrival at 9:00).
for i in range(n):
    loc = friends[i]["location"]
    travel_from_fd = travel_times[("Financial District", loc)]
    opt.add(Implies(And(scheduled[i], order_vars[i] == 1),
                    start_vars[i] >= travel_from_fd))

# Objective: maximize the total number of meetings scheduled.
objective = Sum([If(s, 1, 0) for s in scheduled])
opt.maximize(objective)

if opt.check() == sat:
    model = opt.model()
    meetings = []
    for i, friend in enumerate(friends):
        if is_true(model.evaluate(scheduled[i])):
            order_val = model.evaluate(order_vars[i]).as_long()
            start_val = model.evaluate(start_vars[i]).as_long()
            end_val = model.evaluate(end_vars[i]).as_long()
            meetings.append((order_val, friend["name"], friend["location"], start_val, end_val))
    # Sort the meetings by their order in the itinerary.
    meetings.sort(key=lambda x: x[0])
    itinerary = []
    for order_val, person, location, s, e in meetings:
        itinerary.append({
            "action": "meet",
            "location": location,
            "person": person,
            "start_time": convert_time(s),
            "end_time": convert_time(e)
        })
    output = {"itinerary": itinerary}
    print(json.dumps(output))
else:
    print(json.dumps({"itinerary": []}))