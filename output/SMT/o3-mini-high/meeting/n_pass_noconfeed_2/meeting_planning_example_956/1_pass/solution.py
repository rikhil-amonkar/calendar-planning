from z3 import Optimize, Int, Bool, If, And, Or, Implies, sat
import json

def minutes_to_str(m):
    hr = m // 60
    mn = m % 60
    return f"{hr}:{mn:02d}"

# Travel times in minutes between locations, as provided.
travel_times = {
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Richmond District"): 16,
    ("The Castro", "Financial District"): 21,
    ("The Castro", "Union Square"): 19,
    ("The Castro", "Fisherman's Wharf"): 24,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "Haight-Ashbury"): 6,
    ("The Castro", "Mission District"): 7,
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Golden Gate Park"): 11,

    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "Richmond District"): 11,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "Union Square"): 14,
    ("Alamo Square", "Fisherman's Wharf"): 19,
    ("Alamo Square", "Marina District"): 15,
    ("Alamo Square", "Haight-Ashbury"): 5,
    ("Alamo Square", "Mission District"): 10,
    ("Alamo Square", "Pacific Heights"): 10,
    ("Alamo Square", "Golden Gate Park"): 9,

    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "Alamo Square"): 13,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "Union Square"): 21,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "Haight-Ashbury"): 10,
    ("Richmond District", "Mission District"): 20,
    ("Richmond District", "Pacific Heights"): 10,
    ("Richmond District", "Golden Gate Park"): 9,

    ("Financial District", "The Castro"): 20,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "Union Square"): 9,
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Haight-Ashbury"): 19,
    ("Financial District", "Mission District"): 17,
    ("Financial District", "Pacific Heights"): 13,
    ("Financial District", "Golden Gate Park"): 23,

    ("Union Square", "The Castro"): 17,
    ("Union Square", "Alamo Square"): 15,
    ("Union Square", "Richmond District"): 20,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Fisherman's Wharf"): 15,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "Haight-Ashbury"): 18,
    ("Union Square", "Mission District"): 14,
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "Golden Gate Park"): 22,

    ("Fisherman's Wharf", "The Castro"): 27,
    ("Fisherman's Wharf", "Alamo Square"): 21,
    ("Fisherman's Wharf", "Richmond District"): 18,
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Fisherman's Wharf", "Union Square"): 13,
    ("Fisherman's Wharf", "Marina District"): 9,
    ("Fisherman's Wharf", "Haight-Ashbury"): 22,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,

    ("Marina District", "The Castro"): 22,
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Fisherman's Wharf"): 10,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Mission District"): 20,
    ("Marina District", "Pacific Heights"): 7,
    ("Marina District", "Golden Gate Park"): 18,

    ("Haight-Ashbury", "The Castro"): 6,
    ("Haight-Ashbury", "Alamo Square"): 5,
    ("Haight-Ashbury", "Richmond District"): 10,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Haight-Ashbury", "Union Square"): 19,
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Haight-Ashbury", "Golden Gate Park"): 7,

    ("Mission District", "The Castro"): 7,
    ("Mission District", "Alamo Square"): 11,
    ("Mission District", "Richmond District"): 20,
    ("Mission District", "Financial District"): 15,
    ("Mission District", "Union Square"): 15,
    ("Mission District", "Fisherman's Wharf"): 22,
    ("Mission District", "Marina District"): 19,
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Golden Gate Park"): 17,

    ("Pacific Heights", "The Castro"): 16,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Richmond District"): 12,
    ("Pacific Heights", "Financial District"): 13,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "Marina District"): 6,
    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Golden Gate Park"): 15,

    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Alamo Square"): 9,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Mission District"): 17,
    ("Golden Gate Park", "Pacific Heights"): 16,
}

# Friend meeting constraints
friends = [
    {"name": "William", "location": "Alamo Square", "avail_start": 915, "avail_end": 1035, "min_duration": 60},
    {"name": "Joshua", "location": "Richmond District", "avail_start": 420, "avail_end": 1200, "min_duration": 15},
    {"name": "Joseph", "location": "Financial District", "avail_start": 675, "avail_end": 810, "min_duration": 15},
    {"name": "David", "location": "Union Square", "avail_start": 1005, "avail_end": 1155, "min_duration": 45},
    {"name": "Brian", "location": "Fisherman's Wharf", "avail_start": 825, "avail_end": 1245, "min_duration": 105},
    {"name": "Karen", "location": "Marina District", "avail_start": 690, "avail_end": 1110, "min_duration": 15},
    {"name": "Anthony", "location": "Haight-Ashbury", "avail_start": 435, "avail_end": 630, "min_duration": 30},
    {"name": "Matthew", "location": "Mission District", "avail_start": 1035, "avail_end": 1155, "min_duration": 120},
    {"name": "Helen", "location": "Pacific Heights", "avail_start": 480, "avail_end": 720, "min_duration": 75},
    {"name": "Jeffrey", "location": "Golden Gate Park", "avail_start": 1140, "avail_end": 1290, "min_duration": 60}
]

# Initialize the optimizer (we use Optimize to maximize the number of meetings)
opt = Optimize()

n = len(friends)
start_vars = []
end_vars = []
chosen_vars = []

# Create decision variables for each friend meeting
for i, friend in enumerate(friends):
    s = Int(f"start_{i}")
    e = Int(f"end_{i}")
    c = Bool(f"chosen_{i}")
    start_vars.append(s)
    end_vars.append(e)
    chosen_vars.append(c)
    # If meeting is scheduled, it must occur within the friend's available window 
    opt.add(Or(Not(c), s >= friend["avail_start"]))
    opt.add(Or(Not(c), e <= friend["avail_end"]))
    opt.add(Or(Not(c), e - s >= friend["min_duration"]))

# Arrival: You arrive at "The Castro" at 9:00 AM (540 minutes)
arrival = 540

# For each meeting, if it is the first in the schedule then it must be reachable from the arrival point.
for i, friend in enumerate(friends):
    conds = []
    for j in range(n):
        if i != j:
            conds.append(Or(Not(chosen_vars[j]), start_vars[i] <= start_vars[j]))
    opt.add(Implies(And(chosen_vars[i], And(*conds)),
                    start_vars[i] >= arrival + travel_times[("The Castro", friend["location"])]))

# For any two selected meetings, ensure that travel time between locations is respected.
for i in range(n):
    for j in range(i+1, n):
        loc_i = friends[i]["location"]
        loc_j = friends[j]["location"]
        t_ij = travel_times[(loc_i, loc_j)]
        t_ji = travel_times[(loc_j, loc_i)]
        opt.add(Implies(And(chosen_vars[i], chosen_vars[j]),
                        Or(end_vars[i] + t_ij <= start_vars[j],
                           end_vars[j] + t_ji <= start_vars[i])))

# Objective: maximize the number of meetings scheduled.
opt.maximize(sum([If(c, 1, 0) for c in chosen_vars]))

if opt.check() == sat:
    model = opt.model()
    itinerary = []
    selected = []
    for i, friend in enumerate(friends):
        if model.evaluate(chosen_vars[i]):
            s_val = model.evaluate(start_vars[i]).as_long()
            e_val = model.evaluate(end_vars[i]).as_long()
            selected.append((s_val, e_val, friend))
    # Sort meetings by start time
    selected.sort(key=lambda x: x[0])
    for s_val, e_val, friend in selected:
        itinerary.append({
            "action": "meet",
            "location": friend["location"],
            "person": friend["name"],
            "start_time": minutes_to_str(s_val),
            "end_time": minutes_to_str(e_val)
        })
    output = {"itinerary": itinerary}
    print(json.dumps(output))
else:
    print(json.dumps({"itinerary": []}))