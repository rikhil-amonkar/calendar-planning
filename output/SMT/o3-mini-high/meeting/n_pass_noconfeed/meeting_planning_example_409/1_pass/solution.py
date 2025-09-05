from z3 import *
import json

def minutes_to_time(m):
    h = m // 60
    m_ = m % 60
    return f"{h}:{m_:02d}"

# Friend meeting data: each friend with availability and minimum meeting duration 
friends = [
    {"name": "Thomas", "location": "Bayview", "avail_start": 15*60+30, "avail_end": 18*60+30, "min_dur": 120},
    {"name": "Stephanie", "location": "Golden Gate Park", "avail_start": 18*60+30, "avail_end": 21*60+45, "min_dur": 30},
    {"name": "Laura", "location": "Nob Hill", "avail_start": 8*60+45, "avail_end": 16*60+15, "min_dur": 30},
    {"name": "Betty", "location": "Marina District", "avail_start": 18*60+45, "avail_end": 21*60+45, "min_dur": 45},
    {"name": "Patricia", "location": "Embarcadero", "avail_start": 17*60+30, "avail_end": 22*60, "min_dur": 45},
]
n_friends = len(friends)

# Travel times (in minutes) between locations
travel_times = {
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "Marina District"): 9,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Bayview", "Golden Gate Park"): 22,
    ("Bayview", "Nob Hill"): 20,
    ("Bayview", "Marina District"): 25,
    ("Bayview", "Embarcadero"): 19,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Bayview"): 23,
    ("Golden Gate Park", "Nob Hill"): 20,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Nob Hill", "Fisherman's Wharf"): 11,
    ("Nob Hill", "Bayview"): 19,
    ("Nob Hill", "Golden Gate Park"): 17,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "Embarcadero"): 9,
    ("Marina District", "Fisherman's Wharf"): 10,
    ("Marina District", "Bayview"): 27,
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Embarcadero"): 14,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Embarcadero", "Bayview"): 21,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "Marina District"): 12,
}

# Create an Optimize solver
opt = Optimize()

# Decision variables for each friend:
# scheduled[i]: whether to meet friend i
# s_vars[i]: start time of meeting (in minutes from midnight)
# e_vars[i]: end time of meeting
# order_vars[i]: order of meeting in the schedule (0 if not scheduled, otherwise a positive integer)
scheduled = [Bool(f"scheduled_{i}") for i in range(n_friends)]
s_vars = [Int(f"s_{i}") for i in range(n_friends)]
e_vars = [Int(f"e_{i}") for i in range(n_friends)]
order_vars = [Int(f"order_{i}") for i in range(n_friends)]

# Add basic constraints for each friend meeting if scheduled
for i, friend in enumerate(friends):
    # If not scheduled, force order to be 0; if scheduled, order must be > 0 and at most n_friends.
    opt.add(Implies(scheduled[i], order_vars[i] > 0))
    opt.add(Implies(Not(scheduled[i]), order_vars[i] == 0))
    opt.add(Implies(scheduled[i], order_vars[i] <= n_friends))
    
    # If scheduled, meeting time must lie inside friend's available window with minimum duration.
    opt.add(Implies(scheduled[i],
                    And(s_vars[i] >= friend["avail_start"],
                        e_vars[i] <= friend["avail_end"],
                        e_vars[i] - s_vars[i] >= friend["min_dur"])))
    # Domain constraints for meeting times to be within the day.
    opt.add(s_vars[i] >= 0, s_vars[i] <= 1440)
    opt.add(e_vars[i] >= 0, e_vars[i] <= 1440)

# Enforce distinct ordering for any two scheduled meetings and ensure "dense" ordering.
for i in range(n_friends):
    for j in range(i+1, n_friends):
        opt.add(Implies(And(scheduled[i], scheduled[j]), order_vars[i] != order_vars[j]))
    # Dense order: if a meeting has order > 1 then there must be another meeting with order exactly one less.
    opt.add(Implies(And(scheduled[i], order_vars[i] > 1),
                    Or([And(scheduled[j], order_vars[j] == order_vars[i] - 1) for j in range(n_friends) if j != i])))

# Constraints for travel times between meetings.
# For any two distinct meetings i and j, if j immediately follows i then
# meeting j must start after i ends plus the travel time from i's location to j's location.
for i in range(n_friends):
    for j in range(n_friends):
        if i != j:
            loc_i = friends[i]["location"]
            loc_j = friends[j]["location"]
            travel_time_ij = travel_times[(loc_i, loc_j)]
            opt.add(Implies(And(scheduled[i], scheduled[j], order_vars[j] == order_vars[i] + 1),
                            s_vars[j] >= e_vars[i] + travel_time_ij))

# For the first meeting in the schedule, account for travel time from the initial location.
# Arrival at Fisherman's Wharf is at 9:00 AM (540 minutes).
for i in range(n_friends):
    loc_i = friends[i]["location"]
    travel_time_from_fw = travel_times[("Fisherman's Wharf", loc_i)]
    opt.add(Implies(And(scheduled[i], order_vars[i] == 1),
                    s_vars[i] >= 540 + travel_time_from_fw))

# Objective: maximize the number of friends met.
opt.maximize(Sum([If(scheduled[i], 1, 0) for i in range(n_friends)]))

# Solve and extract the model.
if opt.check() == sat:
    model = opt.model()
    schedule = []
    for i in range(n_friends):
        if is_true(model.eval(scheduled[i])):
            order_val = model.eval(order_vars[i]).as_long()
            s_val = model.eval(s_vars[i]).as_long()
            e_val = model.eval(e_vars[i]).as_long()
            schedule.append((order_val, friends[i]["name"], friends[i]["location"], s_val, e_val))
    # Sort the meetings by their order.
    schedule.sort(key=lambda x: x[0])
    
    itinerary = []
    for order_val, name, location, s_val, e_val in schedule:
        itinerary.append({
            "action": "meet",
            "location": location,
            "person": name,
            "start_time": minutes_to_time(s_val),
            "end_time": minutes_to_time(e_val)
        })
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    print(json.dumps({"itinerary": []}))