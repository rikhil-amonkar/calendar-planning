import json
from z3 import *

def format_time(t):
    # t is minutes after 9:00
    hour = 9 + (t // 60)
    minute = t % 60
    return f"{hour}:{minute:02d}"

# Meeting data: times are in minutes after 9:00.
# Available windows and required durations:
# Ronald: available 13:45 (285) to 17:15 (495), duration 105
# Patricia: available 9:15 (15) to 22:00 (780), duration 60
# Laura: available 12:30 (210) to 12:45 (225), duration 15
# Emily: available 16:15 (435) to 18:30 (570), duration 60
# Mary: available 15:00 (360) to 16:30 (450), duration 60
meetings_data = [
    {"name": "Ronald", "location": "Russian Hill", "avail_start": 285, "avail_end": 495, "duration": 105},
    {"name": "Patricia", "location": "Sunset District", "avail_start": 15, "avail_end": 780, "duration": 60},
    {"name": "Laura", "location": "North Beach", "avail_start": 210, "avail_end": 225, "duration": 15},
    {"name": "Emily", "location": "The Castro", "avail_start": 435, "avail_end": 570, "duration": 60},
    {"name": "Mary", "location": "Golden Gate Park", "avail_start": 360, "avail_end": 450, "duration": 60}
]

# Travel times (in minutes) between locations (and from Financial District)
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
    ("Golden Gate Park", "The Castro"): 13
}

# Create an Optimize solver for optimization
opt = Optimize()

# For each meeting we create:
#  - a Boolean variable indicating if the meeting is scheduled (x)
#  - an integer variable s for start time (minutes after 9:00)
#  - an integer variable order (0 if not scheduled, otherwise 1..N)
meeting_vars = {}
for meeting in meetings_data:
    name = meeting["name"]
    x = Bool(name + "_scheduled")
    s = Int(name + "_start")   # start time (in minutes after 9:00)
    order = Int(name + "_order")
    meeting_vars[name] = {"data": meeting, "x": x, "s": s, "order": order}
    # If not scheduled, force order = 0.
    opt.add(Implies(Not(x), order == 0))
    # If scheduled, order is between 1 and the total number of meetings.
    opt.add(Implies(x, And(order >= 1, order <= len(meetings_data))))
    # Meeting must occur within friend availability if scheduled.
    opt.add(Implies(x, meeting["avail_start"] <= s))
    opt.add(Implies(x, s + meeting["duration"] <= meeting["avail_end"]))
    # Start time is nonnegative.
    opt.add(s >= 0)

# Ensure that if two meetings are scheduled they get unique order numbers.
names = list(meeting_vars.keys())
for i in range(len(names)):
    for j in range(i+1, len(names)):
        mi = meeting_vars[names[i]]
        mj = meeting_vars[names[j]]
        opt.add(Implies(And(mi["x"], mj["x"]), mi["order"] != mj["order"]))

# Add constraint: for the first meeting in the schedule (order == 1),
# the start time must be after arrival at the meeting location from the Financial District.
for name in names:
    mvar = meeting_vars[name]
    loc = mvar["data"]["location"]
    travel_from_fd = travel_times[("Financial District", loc)]
    opt.add(Implies(And(mvar["x"], mvar["order"] == 1), mvar["s"] >= travel_from_fd))

# For any two meetings, if one immediately follows the other (orders differ by 1),
# then the later meeting's start time must be at least the earlier meeting's end time plus travel time.
for name_i in names:
    for name_j in names:
        if name_i == name_j:
            continue
        mi = meeting_vars[name_i]
        mj = meeting_vars[name_j]
        travel_ij = travel_times[(mi["data"]["location"], mj["data"]["location"])]
        opt.add(Implies(And(mi["x"], mj["x"], mj["order"] == mi["order"] + 1),
                        mj["s"] >= mi["s"] + mi["data"]["duration"] + travel_ij))

# For every scheduled meeting with order > 1, ensure that there is some scheduled meeting
# that immediately precedes it (i.e. has order = current order - 1).
for name_i in names:
    mi = meeting_vars[name_i]
    preds = []
    for name_j in names:
        if name_i == name_j:
            continue
        mj = meeting_vars[name_j]
        preds.append(And(mj["x"], mj["order"] == mi["order"] - 1))
    if preds:
        opt.add(Implies(And(mi["x"], mi["order"] > 1), Or(preds)))

# Objective: maximize the total number of scheduled meetings.
total_meetings = Sum([If(meeting_vars[name]["x"], 1, 0) for name in names])
opt.maximize(total_meetings)

# Solve the model.
if opt.check() == sat:
    m = opt.model()
    # Collect scheduled meetings and sort them by their order.
    scheduled = []
    for name in names:
        mvar = meeting_vars[name]
        if is_true(m.evaluate(mvar["x"])):
            order_val = m.evaluate(mvar["order"]).as_long()
            start_val = m.evaluate(mvar["s"]).as_long()
            duration = mvar["data"]["duration"]
            scheduled.append((order_val, name, mvar["data"]["location"], start_val, start_val + duration))
    scheduled.sort(key=lambda x: x[0])
    itinerary = []
    for order_val, person, location, start, end in scheduled:
        itinerary.append({
            "action": "meet",
            "location": location,
            "person": person,
            "start_time": format_time(start),
            "end_time": format_time(end)
        })
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    # If no schedule is feasible, output an empty itinerary.
    print(json.dumps({"itinerary": []}))