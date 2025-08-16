from z3 import *
import json

# Define the friend data.
# Times are expressed in minutes from midnight.
friends = [
    {"name": "Matthew", "location": "The Castro", "avail_start": 16 * 60 + 30, "avail_end": 20 * 60, "duration": 45},
    {"name": "Rebecca", "location": "Nob Hill", "avail_start": 15 * 60 + 15, "avail_end": 19 * 60 + 15, "duration": 105},
    {"name": "Brian", "location": "Marina District", "avail_start": 14 * 60 + 15, "avail_end": 22 * 60, "duration": 30},
    {"name": "Emily", "location": "Pacific Heights", "avail_start": 11 * 60 + 15, "avail_end": 19 * 60 + 45, "duration": 15},
    {"name": "Karen", "location": "Haight-Ashbury", "avail_start": 11 * 60 + 45, "avail_end": 17 * 60 + 30, "duration": 30},
    {"name": "Stephanie", "location": "Mission District", "avail_start": 13 * 60, "avail_end": 15 * 60 + 45, "duration": 75},
    {"name": "James", "location": "Chinatown", "avail_start": 14 * 60 + 30, "avail_end": 19 * 60, "duration": 120},
    {"name": "Steven", "location": "Russian Hill", "avail_start": 14 * 60, "avail_end": 20 * 60, "duration": 30},
    {"name": "Elizabeth", "location": "Alamo Square", "avail_start": 13 * 60, "avail_end": 17 * 60 + 15, "duration": 120},
    {"name": "William", "location": "Bayview", "avail_start": 18 * 60 + 15, "avail_end": 20 * 60 + 15, "duration": 90},
]

# Travel times (in minutes) between neighborhoods.
# Note: Not all travel times are symmetric.
travel = {
    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "Nob Hill"): 17,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "Pacific Heights"): 10,
    ("Richmond District", "Haight-Ashbury"): 10,
    ("Richmond District", "Mission District"): 20,
    ("Richmond District", "Chinatown"): 20,
    ("Richmond District", "Russian Hill"): 13,
    ("Richmond District", "Alamo Square"): 13,
    ("Richmond District", "Bayview"): 27,
    ("The Castro", "Richmond District"): 16,
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Haight-Ashbury"): 6,
    ("The Castro", "Mission District"): 7,
    ("The Castro", "Chinatown"): 22,
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Bayview"): 19,
    ("Nob Hill", "Richmond District"): 14,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "Haight-Ashbury"): 13,
    ("Nob Hill", "Mission District"): 13,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "Russian Hill"): 5,
    ("Nob Hill", "Alamo Square"): 11,
    ("Nob Hill", "Bayview"): 19,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Pacific Heights"): 7,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Mission District"): 20,
    ("Marina District", "Chinatown"): 15,
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Bayview"): 27,
    ("Pacific Heights", "Richmond District"): 12,
    ("Pacific Heights", "The Castro"): 16,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Marina District"): 6,
    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "Russian Hill"): 7,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Bayview"): 22,
    ("Haight-Ashbury", "Richmond District"): 10,
    ("Haight-Ashbury", "The Castro"): 6,
    ("Haight-Ashbury", "Nob Hill"): 15,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Chinatown"): 19,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "Alamo Square"): 5,
    ("Haight-Ashbury", "Bayview"): 18,
    ("Mission District", "Richmond District"): 20,
    ("Mission District", "The Castro"): 7,
    ("Mission District", "Nob Hill"): 12,
    ("Mission District", "Marina District"): 19,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Chinatown"): 16,
    ("Mission District", "Russian Hill"): 15,
    ("Mission District", "Alamo Square"): 11,
    ("Mission District", "Bayview"): 14,
    ("Chinatown", "Richmond District"): 20,
    ("Chinatown", "The Castro"): 22,
    ("Chinatown", "Nob Hill"): 9,
    ("Chinatown", "Marina District"): 12,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "Haight-Ashbury"): 19,
    ("Chinatown", "Mission District"): 17,
    ("Chinatown", "Russian Hill"): 7,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Bayview"): 20,
    ("Russian Hill", "Richmond District"): 14,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Nob Hill"): 5,
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "Pacific Heights"): 7,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "Mission District"): 16,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Bayview"): 23,
    ("Alamo Square", "Richmond District"): 11,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "Nob Hill"): 11,
    ("Alamo Square", "Marina District"): 15,
    ("Alamo Square", "Pacific Heights"): 10,
    ("Alamo Square", "Haight-Ashbury"): 5,
    ("Alamo Square", "Mission District"): 10,
    ("Alamo Square", "Chinatown"): 15,
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "Bayview"): 16,
    ("Bayview", "Richmond District"): 25,
    ("Bayview", "The Castro"): 19,
    ("Bayview", "Nob Hill"): 20,
    ("Bayview", "Marina District"): 27,
    ("Bayview", "Pacific Heights"): 23,
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Mission District"): 13,
    ("Bayview", "Chinatown"): 19,
    ("Bayview", "Russian Hill"): 23,
    ("Bayview", "Alamo Square"): 16,
}

# Helper function: get travel time from one location to another.
def get_travel_time(from_loc, to_loc):
    return travel.get((from_loc, to_loc), 9999)  # A very high cost if not defined

# Create an Optimize() object.
opt = Optimize()
n = len(friends)

# Decision variables:
# - scheduled[i]: whether friend i is met.
# - s_vars[i], e_vars[i]: start and end times for the meeting (in minutes from midnight).
# - order_vars[i]: an integer representing the sequence order if scheduled; if not scheduled, we set it to -1.
scheduled = [Bool(f"scheduled_{i}") for i in range(n)]
s_vars = [Int(f"s_{i}") for i in range(n)]
e_vars = [Int(f"e_{i}") for i in range(n)]
order_vars = [Int(f"order_{i}") for i in range(n)]

initial_time = 9 * 60  # 9:00 AM => 540 minutes

# For each friend, if the meeting is scheduled then it must happen within the friend’s availability window
# and last at least the minimum duration. Otherwise, we force the meeting times to 0.
for i, friend in enumerate(friends):
    a_start = friend["avail_start"]
    a_end = friend["avail_end"]
    dur = friend["duration"]
    opt.add(Implies(scheduled[i], s_vars[i] >= a_start))
    opt.add(Implies(scheduled[i], e_vars[i] <= a_end))
    opt.add(Implies(scheduled[i], e_vars[i] - s_vars[i] >= dur))
    opt.add(Implies(Not(scheduled[i]), s_vars[i] == 0))
    opt.add(Implies(Not(scheduled[i]), e_vars[i] == 0))
    # If scheduled, order must be within [0, n-1]; if not scheduled, we set it to -1.
    opt.add(Implies(scheduled[i], And(order_vars[i] >= 0, order_vars[i] < n)))
    opt.add(Implies(Not(scheduled[i]), order_vars[i] == -1))

# Enforce that scheduled meetings get distinct order values.
for i in range(n):
    for j in range(i + 1, n):
        opt.add(Implies(And(scheduled[i], scheduled[j]), order_vars[i] != order_vars[j]))

# Consecutive travel constraints:
# If meeting i comes immediately before meeting j (i.e. order[j] == order[i] + 1) then the start of meeting j
# must be at least the end of meeting i plus the travel time from i’s location to j’s location.
for i in range(n):
    for j in range(n):
        if i != j:
            travel_ij = get_travel_time(friends[i]["location"], friends[j]["location"])
            opt.add(Implies(And(scheduled[i], scheduled[j], order_vars[j] == order_vars[i] + 1),
                            s_vars[j] >= e_vars[i] + travel_ij))

# For the first meeting in the sequence (order == 0), the meeting must be reachable from Richmond District.
for i, friend in enumerate(friends):
    travel_from_start = get_travel_time("Richmond District", friend["location"])
    opt.add(Implies(And(scheduled[i], order_vars[i] == 0),
                    s_vars[i] >= initial_time + travel_from_start))

# Enforce contiguity of the ordering.
# For each potential order k > 0, if any meeting gets order k then some meeting must have order k - 1.
for k in range(1, n):
    cnt_k = Sum([If(order_vars[i] == k, 1, 0) for i in range(n)])
    cnt_k_minus = Sum([If(order_vars[i] == k - 1, 1, 0) for i in range(n)])
    opt.add(Implies(cnt_k >= 1, cnt_k_minus >= 1))

# Objective: maximize the total number of meetings scheduled.
num_scheduled = Sum([If(scheduled[i], 1, 0) for i in range(n)])
opt.maximize(num_scheduled)

# Check for attainment of an optimal schedule.
if opt.check() == sat:
    model = opt.model()
    schedule = []
    for i in range(n):
        if is_true(model.evaluate(scheduled[i])):
            order_val = model.evaluate(order_vars[i]).as_long()
            start_val = model.evaluate(s_vars[i]).as_long()
            end_val = model.evaluate(e_vars[i]).as_long()
            schedule.append((order_val, friends[i]["name"], start_val, end_val))
    # Sort meetings by their order in the route.
    schedule.sort(key=lambda x: x[0])

    # Convert minutes (from midnight) to HH:MM format.
    def minutes_to_time(m):
        hh = m // 60
        mm = m % 60
        return f"{hh:02d}:{mm:02d}"

    itinerary = []
    for order_val, name, s_val, e_val in schedule:
        itinerary.append({
            "action": "meet",
            "person": name,
            "start_time": minutes_to_time(s_val),
            "end_time": minutes_to_time(e_val)
        })

    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=4))
else:
    print("No solution found")