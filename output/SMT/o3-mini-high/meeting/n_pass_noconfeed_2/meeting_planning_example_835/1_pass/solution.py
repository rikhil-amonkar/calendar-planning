from z3 import *
import json

# Define friends' meeting constraints
# Times are represented in minutes from midnight
# 9:00 AM is 540 minutes.
friends = [
    {"name": "Helen", "location": "Golden Gate Park", "avail_start": 570, "avail_end": 735, "dur": 45},
    {"name": "Steven", "location": "The Castro", "avail_start": 1215, "avail_end": 1320, "dur": 105},
    {"name": "Deborah", "location": "Bayview", "avail_start": 510, "avail_end": 720, "dur": 30},
    {"name": "Matthew", "location": "Marina District", "avail_start": 555, "avail_end": 855, "dur": 45},
    {"name": "Joseph", "location": "Union Square", "avail_start": 855, "avail_end": 1125, "dur": 120},
    {"name": "Ronald", "location": "Sunset District", "avail_start": 960, "avail_end": 1245, "dur": 60},
    {"name": "Robert", "location": "Alamo Square", "avail_start": 1110, "avail_end": 1275, "dur": 120},
    {"name": "Rebecca", "location": "Financial District", "avail_start": 885, "avail_end": 975, "dur": 30},
    {"name": "Elizabeth", "location": "Mission District", "avail_start": 1110, "avail_end": 1260, "dur": 120}
]

# Define travel times (in minutes) between locations
travel_times = {
    "Pacific Heights": {
        "Golden Gate Park": 15,
        "The Castro": 16,
        "Bayview": 22,
        "Marina District": 6,
        "Union Square": 12,
        "Sunset District": 21,
        "Alamo Square": 10,
        "Financial District": 13,
        "Mission District": 15
    },
    "Golden Gate Park": {
        "Pacific Heights": 16,
        "The Castro": 13,
        "Bayview": 23,
        "Marina District": 16,
        "Union Square": 22,
        "Sunset District": 10,
        "Alamo Square": 9,
        "Financial District": 26,
        "Mission District": 17
    },
    "The Castro": {
        "Pacific Heights": 16,
        "Golden Gate Park": 11,
        "Bayview": 19,
        "Marina District": 21,
        "Union Square": 19,
        "Sunset District": 17,
        "Alamo Square": 8,
        "Financial District": 21,
        "Mission District": 7
    },
    "Bayview": {
        "Pacific Heights": 23,
        "Golden Gate Park": 22,
        "The Castro": 19,
        "Marina District": 27,
        "Union Square": 18,
        "Sunset District": 23,
        "Alamo Square": 16,
        "Financial District": 19,
        "Mission District": 13
    },
    "Marina District": {
        "Pacific Heights": 7,
        "Golden Gate Park": 18,
        "The Castro": 22,
        "Bayview": 27,
        "Union Square": 16,
        "Sunset District": 19,
        "Alamo Square": 15,
        "Financial District": 17,
        "Mission District": 20
    },
    "Union Square": {
        "Pacific Heights": 15,
        "Golden Gate Park": 22,
        "The Castro": 17,
        "Bayview": 15,
        "Marina District": 18,
        "Sunset District": 27,
        "Alamo Square": 15,
        "Financial District": 9,
        "Mission District": 14
    },
    "Sunset District": {
        "Pacific Heights": 21,
        "Golden Gate Park": 11,
        "The Castro": 17,
        "Bayview": 22,
        "Marina District": 21,
        "Union Square": 30,
        "Alamo Square": 17,
        "Financial District": 30,
        "Mission District": 25
    },
    "Alamo Square": {
        "Pacific Heights": 10,
        "Golden Gate Park": 9,
        "The Castro": 8,
        "Bayview": 16,
        "Marina District": 15,
        "Union Square": 14,
        "Sunset District": 16,
        "Financial District": 17,
        "Mission District": 10
    },
    "Financial District": {
        "Pacific Heights": 13,
        "Golden Gate Park": 23,
        "The Castro": 20,
        "Bayview": 19,
        "Marina District": 15,
        "Union Square": 9,
        "Sunset District": 30,
        "Alamo Square": 17,
        "Mission District": 17
    },
    "Mission District": {
        "Pacific Heights": 16,
        "Golden Gate Park": 17,
        "The Castro": 7,
        "Bayview": 14,
        "Marina District": 19,
        "Union Square": 15,
        "Sunset District": 24,
        "Alamo Square": 11,
        "Financial District": 15
    }
}

# Create the optimizer
opt = Optimize()

n = len(friends)

# Decision variable: x[i] is True if meeting with friend i is scheduled.
x = [Bool(f"meet_{i}") for i in range(n)]

# Decision variable: start[i] is the start time (in minutes from midnight) of meeting with friend i.
start = [Int(f"start_{i}") for i in range(n)]

# Create Boolean ordering variables: before[(i,j)] is True if meeting i is scheduled before meeting j.
before = {}
for i in range(n):
    for j in range(n):
        if i != j:
            before[(i, j)] = Bool(f"before_{i}_{j}")

# For each scheduled meeting, impose the friend’s availability and minimum meeting duration constraints.
for i in range(n):
    f = friends[i]
    # Meeting must not start before the friend's availability.
    opt.add(Implies(x[i], start[i] >= f["avail_start"]))
    # Meeting must end (start + duration) by the friend's end time.
    opt.add(Implies(x[i], start[i] + f["dur"] <= f["avail_end"]))

# Impose ordering constraints between every pair of scheduled meetings.
for i in range(n):
    for j in range(i+1, n):
        # If both meetings are scheduled then one must come before the other.
        opt.add(Implies(And(x[i], x[j]), Or(before[(i, j)], before[(j, i)])))
        # Consistency: if both scheduled, then before[i,j] is the negation of before[j,i].
        opt.add(Implies(And(x[i], x[j]), before[(i, j)] == Not(before[(j, i)])))
        # If meeting i comes before meeting j, account for meeting duration and travel.
        travel_ij = travel_times[friends[i]["location"]][friends[j]["location"]]
        travel_ji = travel_times[friends[j]["location"]][friends[i]["location"]]
        opt.add(Implies(And(x[i], x[j], before[(i, j)]),
                         start[i] + friends[i]["dur"] + travel_ij <= start[j]))
        opt.add(Implies(And(x[i], x[j], before[(j, i)]),
                         start[j] + friends[j]["dur"] + travel_ji <= start[i]))

# For the first meeting (with no preceding meeting) we must travel from Pacific Heights.
for i in range(n):
    travel_from_start = travel_times["Pacific Heights"][friends[i]["location"]]
    # is_first: meeting i is scheduled and no other scheduled meeting comes before it.
    is_first = And(x[i], *[Or(Not(x[j]), Not(before[(j, i)])) for j in range(n) if j != i])
    opt.add(Implies(is_first, start[i] >= 540 + travel_from_start))

# Objective: maximize the number of meetings scheduled.
total_meetings = Sum([If(x[i], 1, 0) for i in range(n)])
opt.maximize(total_meetings)

# Check for a solution and get the model.
if opt.check() == sat:
    model = opt.model()
else:
    print(json.dumps({"itinerary": []}))
    exit(0)

# Extract the scheduled meetings with their start times.
scheduled = []
for i in range(n):
    if is_true(model.evaluate(x[i])):
        s_val = model.evaluate(start[i]).as_long()
        scheduled.append({
            "person": friends[i]["name"],
            "location": friends[i]["location"],
            "start": s_val,
            "end": s_val + friends[i]["dur"]
        })

# Sort the scheduled meetings by their start time.
scheduled.sort(key=lambda m: m["start"])

def minutes_to_time_str(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

# Build the itinerary JSON list.
itinerary = []
for m in scheduled:
    itinerary.append({
        "action": "meet",
        "location": m["location"],
        "person": m["person"],
        "start_time": minutes_to_time_str(m["start"]),
        "end_time": minutes_to_time_str(m["end"])
    })

result = {"itinerary": itinerary}
print(json.dumps(result))