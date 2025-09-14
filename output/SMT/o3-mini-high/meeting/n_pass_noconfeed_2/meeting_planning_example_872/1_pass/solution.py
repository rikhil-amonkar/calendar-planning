from z3 import *
import json

# -----------------------------
# Helper: Convert minutes (since midnight) into "H:MM" format.
def minutes_to_time(t):
    hours = t // 60
    minutes = t % 60
    return f"{hours}:{minutes:02d}"

# -----------------------------
# Travel times (in minutes) as given.
# Locations: "Presidio", "Haight-Ashbury", "Nob Hill", "Russian Hill",
# "North Beach", "Chinatown", "Union Square", "Embarcadero", "Financial District", "Marina District"
travel_times = {
    "Presidio": {
        "Haight-Ashbury": 15,
        "Nob Hill": 18,
        "Russian Hill": 14,
        "North Beach": 18,
        "Chinatown": 21,
        "Union Square": 22,
        "Embarcadero": 20,
        "Financial District": 23,
        "Marina District": 11
    },
    "Haight-Ashbury": {
        "Presidio": 15,
        "Nob Hill": 15,
        "Russian Hill": 17,
        "North Beach": 19,
        "Chinatown": 19,
        "Union Square": 19,
        "Embarcadero": 20,
        "Financial District": 21,
        "Marina District": 17
    },
    "Nob Hill": {
        "Presidio": 17,
        "Haight-Ashbury": 13,
        "Russian Hill": 5,
        "North Beach": 8,
        "Chinatown": 6,
        "Union Square": 7,
        "Embarcadero": 9,
        "Financial District": 9,
        "Marina District": 11
    },
    "Russian Hill": {
        "Presidio": 14,
        "Haight-Ashbury": 17,
        "Nob Hill": 5,
        "North Beach": 5,
        "Chinatown": 9,
        "Union Square": 10,
        "Embarcadero": 8,
        "Financial District": 11,
        "Marina District": 7
    },
    "North Beach": {
        "Presidio": 17,
        "Haight-Ashbury": 18,
        "Nob Hill": 7,
        "Russian Hill": 4,
        "Chinatown": 6,
        "Union Square": 7,
        "Embarcadero": 6,
        "Financial District": 8,
        "Marina District": 9
    },
    "Chinatown": {
        "Presidio": 19,
        "Haight-Ashbury": 19,
        "Nob Hill": 9,
        "Russian Hill": 7,
        "North Beach": 3,
        "Union Square": 7,
        "Embarcadero": 5,
        "Financial District": 5,
        "Marina District": 12
    },
    "Union Square": {
        "Presidio": 24,
        "Haight-Ashbury": 18,
        "Nob Hill": 9,
        "Russian Hill": 13,
        "North Beach": 10,
        "Chinatown": 7,
        "Embarcadero": 11,
        "Financial District": 9,
        "Marina District": 18
    },
    "Embarcadero": {
        "Presidio": 20,
        "Haight-Ashbury": 21,
        "Nob Hill": 10,
        "Russian Hill": 8,
        "North Beach": 5,
        "Chinatown": 7,
        "Union Square": 10,
        "Financial District": 5,
        "Marina District": 12
    },
    "Financial District": {
        "Presidio": 22,
        "Haight-Ashbury": 19,
        "Nob Hill": 8,
        "Russian Hill": 11,
        "North Beach": 7,
        "Chinatown": 5,
        "Union Square": 9,
        "Embarcadero": 4,
        "Marina District": 15
    },
    "Marina District": {
        "Presidio": 10,
        "Haight-Ashbury": 16,
        "Nob Hill": 12,
        "Russian Hill": 8,
        "North Beach": 11,
        "Chinatown": 15,
        "Union Square": 16,
        "Embarcadero": 14,
        "Financial District": 17
    }
}

# -----------------------------
# Friend meeting data.
# Times are converted into minutes since midnight.
# Format: { "name": ..., "location": ..., "avail_start": ..., "avail_end": ..., "min_duration": ... }
# Note: 9:00 AM is 540, 21:00 is 1260 etc.
friends = [
    {"name": "Karen", "location": "Haight-Ashbury", "avail_start": 1260, "avail_end": 1305, "min_duration": 45},
    {"name": "Jessica", "location": "Nob Hill", "avail_start": 825,  "avail_end": 1260, "min_duration": 90},
    {"name": "Brian", "location": "Russian Hill", "avail_start": 930,  "avail_end": 1305, "min_duration": 60},
    {"name": "Kenneth", "location": "North Beach", "avail_start": 585,  "avail_end": 1260, "min_duration": 30},
    {"name": "Jason", "location": "Chinatown", "avail_start": 495, "avail_end": 705,  "min_duration": 75},
    {"name": "Stephanie", "location": "Union Square", "avail_start": 885, "avail_end": 1125, "min_duration": 105},
    {"name": "Kimberly", "location": "Embarcadero", "avail_start": 585, "avail_end": 1170, "min_duration": 75},
    {"name": "Steven", "location": "Financial District", "avail_start": 435, "avail_end": 1275, "min_duration": 60},
    {"name": "Mark", "location": "Marina District", "avail_start": 615, "avail_end": 780, "min_duration": 75}
]

num_friends = len(friends)

# Precompute travel times from Presidio to each friend's location.
pres_to_friend = []
for i in range(num_friends):
    loc = friends[i]["location"]
    t = travel_times["Presidio"][loc]
    pres_to_friend.append(t)

# Precompute travel times between friends.
# travel_friend[i][j] = travel time from friend i's location to friend j's location.
travel_friend = [[None for _ in range(num_friends)] for _ in range(num_friends)]
for i in range(num_friends):
    loc_i = friends[i]["location"]
    for j in range(num_friends):
        loc_j = friends[j]["location"]
        travel_friend[i][j] = travel_times[loc_i][loc_j]

# -----------------------------
# We will use a permutation formulation to decide the meeting order.
# There are up to num_slots slots. A slot value of -1 indicates "no meeting".
num_slots = num_friends  # maximum possible meetings

# Create decision variables:
# X[k] is the friend index scheduled at slot k (or -1 if slot is empty).
# T[k] is the meeting start time (in minutes) for the meeting in slot k.
X_vars = [Int(f"X_{k}") for k in range(num_slots)]
T_vars = [Int(f"T_{k}") for k in range(num_slots)]

opt = Optimize()

# Domain Constraints for each slot:
for k in range(num_slots):
    # X_vars[k] must be either -1 or in 0..num_friends-1.
    opt.add(Or(X_vars[k] == -1, And(X_vars[k] >= 0, X_vars[k] < num_friends)))
    
    # If slot k is unused, no constraint on time; if used, then meeting must lie within friend's available window.
    for i in range(num_friends):
        # If this slot is assigned friend i, then enforce available time constraints.
        opt.add(Implies(X_vars[k] == i, T_vars[k] >= friends[i]["avail_start"]))
        opt.add(Implies(X_vars[k] == i, T_vars[k] + friends[i]["min_duration"] <= friends[i]["avail_end"]))

    # Optional: bound meeting start times to a reasonable window (e.g., between 0 and 1440).
    opt.add(Implies(X_vars[k] != -1, And(T_vars[k] >= 0, T_vars[k] <= 1440)))

# Special constraint for the first slot:
for i in range(num_friends):
    # If the first slot is friend i, then must be reachable from Presidio.
    opt.add(Implies(X_vars[0] == i, T_vars[0] >= 540 + pres_to_friend[i]))
    
# For subsequent slots: ensure contiguous chain and travel time constraints.
for k in range(1, num_slots):
    # If slot k is used, then the previous slot must be used (no gaps).
    opt.add(Implies(X_vars[k] != -1, X_vars[k-1] != -1))
    
    # For any assignment of slot k-1 = i and slot k = j, enforce travel time constraint.
    for i in range(num_friends):
        for j in range(num_friends):
            travel_time_ij = travel_friend[i][j]
            # If slot k-1 is friend i and slot k is friend j, then meeting k must start after meeting k-1 ends + travel time.
            opt.add(Implies(And(X_vars[k-1] == i, X_vars[k] == j),
                            T_vars[k] >= T_vars[k-1] + friends[i]["min_duration"] + travel_time_ij))
    # Ensure meeting start times are in non-decreasing order if both slots are used.
    opt.add(Implies(And(X_vars[k-1] != -1, X_vars[k] != -1), T_vars[k-1] <= T_vars[k]))
    
    # Enforce contiguity: if a slot is empty then all later slots are empty.
    opt.add(Implies(X_vars[k-1] == -1, X_vars[k] == -1))

# Distinctness: a friend should not appear more than once.
for k in range(num_slots):
    for j in range(k+1, num_slots):
        opt.add(Implies(And(X_vars[k] != -1, X_vars[j] != -1), X_vars[k] != X_vars[j]))

# -----------------------------
# Define objective: maximize number of scheduled meetings.
scheduled_meetings = [If(X_vars[k] != -1, 1, 0) for k in range(num_slots)]
total_meetings = Sum(scheduled_meetings)
h = opt.maximize(total_meetings)

# -----------------------------
# Solve and extract model.
if opt.check() == sat:
    model = opt.model()
    itinerary = []
    # Iterate slots in order; only include slots that are scheduled (not -1)
    for k in range(num_slots):
        slot_val = model.evaluate(X_vars[k]).as_long()
        if slot_val == -1:
            break  # No more meetings scheduled
        t_start = model.evaluate(T_vars[k]).as_long()
        friend = friends[slot_val]
        meeting = {
            "action": "meet",
            "location": friend["location"],
            "person": friend["name"],
            "start_time": minutes_to_time(t_start),
            "end_time": minutes_to_time(t_start + friend["min_duration"])
        }
        itinerary.append(meeting)
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))
else:
    # If no solution is found, output an empty itinerary.
    print(json.dumps({"itinerary": []}, indent=2))