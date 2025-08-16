from z3 import *
import json

# Define travel times between districts as given in the problem.
# We only include those pairs that involve our used locations.
travel_times = {
    ("Union Square", "Presidio"): 24,
    ("Union Square", "Alamo Square"): 15,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Sunset District"): 27,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Russian Hill"): 13,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Haight-Ashbury"): 18,

    ("Presidio", "Alamo Square"): 19,
    ("Presidio", "Marina District"): 11,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Haight-Ashbury"): 15,

    ("Alamo Square", "Presidio"): 14,
    ("Alamo Square", "Marina District"): 15,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "Nob Hill"): 11,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "Chinatown"): 15,
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Haight-Ashbury"): 5,

    ("Marina District", "Presidio"): 10,
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Sunset District"): 19,
    ("Marina District", "Chinatown"): 15,
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "North Beach"): 11,
    ("Marina District", "Haight-Ashbury"): 16,

    ("Financial District", "Presidio"): 22,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Nob Hill"): 8,
    ("Financial District", "Sunset District"): 30,
    ("Financial District", "Chinatown"): 5,
    ("Financial District", "Russian Hill"): 11,
    ("Financial District", "North Beach"): 7,
    ("Financial District", "Haight-Ashbury"): 19,

    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "Alamo Square"): 11,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "Financial District"): 9,
    ("Nob Hill", "Sunset District"): 24,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "Russian Hill"): 5,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Haight-Ashbury"): 13,

    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "Nob Hill"): 27,
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "North Beach"): 28,
    ("Sunset District", "Haight-Ashbury"): 15,

    ("Chinatown", "Presidio"): 7,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Marina District"): 12,
    ("Chinatown", "Financial District"): 5,
    ("Chinatown", "Nob Hill"): 9,
    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "Russian Hill"): 7,
    ("Chinatown", "North Beach"): 3,
    ("Chinatown", "Haight-Ashbury"): 19,

    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "Financial District"): 11,
    ("Russian Hill", "Nob Hill"): 5,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "North Beach"): 5,
    ("Russian Hill", "Haight-Ashbury"): 17,

    ("North Beach", "Presidio"): 18,
    ("North Beach", "Alamo Square"): 15,
    ("North Beach", "Marina District"): 11,
    ("North Beach", "Financial District"): 8,
    ("North Beach", "Nob Hill"): 8,
    ("North Beach", "Sunset District"): 28,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Russian Hill"): 4,
    ("North Beach", "Haight-Ashbury"): 18,

    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "Alamo Square"): 5,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Haight-Ashbury", "Nob Hill"): 15,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Haight-Ashbury", "Chinatown"): 19,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "North Beach"): 19,
}

# Friends with their meeting locations, available time windows (in minutes after midnight)
# and required minimum meeting durations (in minutes). Times:
# 9:00AM = 540, 10:30AM = 630, 12:45PM = 765, 14:00 = 840, 15:30 = 930, etc.
friends = [
    {"name": "Kimberly", "location": "Presidio",         "avail_start": 930,  "avail_end": 960,  "min_duration": 15},   # 15:30-16:00
    {"name": "Elizabeth", "location": "Alamo Square",    "avail_start": 1155, "avail_end": 1215, "min_duration": 15},   # 19:15-20:15
    {"name": "Joshua",    "location": "Marina District", "avail_start": 630,  "avail_end": 855,  "min_duration": 45},   # 10:30-14:15
    {"name": "Sandra",    "location": "Financial District", "avail_start": 1170, "avail_end": 1215, "min_duration": 45},  # 19:30-20:15
    {"name": "Kenneth",   "location": "Nob Hill",        "avail_start": 765,  "avail_end": 1305, "min_duration": 30},   # 12:45-21:45
    {"name": "Betty",     "location": "Sunset District", "avail_start": 840,  "avail_end": 1140, "min_duration": 60},   # 14:00-19:00
    {"name": "Deborah",   "location": "Chinatown",       "avail_start": 1035, "avail_end": 1230, "min_duration": 15},   # 17:15-20:30
    {"name": "Barbara",   "location": "Russian Hill",    "avail_start": 1050, "avail_end": 1275, "min_duration": 120},  # 17:30-21:15
    {"name": "Steven",    "location": "North Beach",     "avail_start": 1065, "avail_end": 1245, "min_duration": 90},   # 17:45-20:45
    {"name": "Daniel",    "location": "Haight-Ashbury",  "avail_start": 1110, "avail_end": 1125, "min_duration": 15},   # 18:30-18:45
]

n = len(friends)

# Create an Optimize instance so we can maximize the number of meetings scheduled.
opt = Optimize()

# For each friend we have a Boolean variable indicating whether we schedule that meeting,
# and Int variables for the meeting start and end times (in minutes from midnight).
decided = [Bool(f"decided_{i}") for i in range(n)]
start_vars = [Int(f"start_{i}") for i in range(n)]
end_vars   = [Int(f"end_{i}") for i in range(n)]

# Add constraints for each friend if the meeting is scheduled.
for i, friend in enumerate(friends):
    # If scheduled then the meeting must start no earlier than the friend’s available start,
    # and end no later than the available end.
    opt.add(Implies(decided[i], start_vars[i] >= friend["avail_start"]))
    opt.add(Implies(decided[i], end_vars[i] <= friend["avail_end"]))
    # The meeting must last at least the minimum required duration.
    opt.add(Implies(decided[i], end_vars[i] - start_vars[i] >= friend["min_duration"]))
    # Additionally, you start the day at Union Square at 09:00.
    # So you must travel from Union Square to the meeting location.
    arrival_time = 540 + travel_times[("Union Square", friend["location"])]
    opt.add(Implies(decided[i], start_vars[i] >= arrival_time))
    # If not scheduled, optionally fix the start time (this simply bounds the variables).
    opt.add(Implies(Not(decided[i]), start_vars[i] == friend["avail_start"]))
    opt.add(Implies(Not(decided[i]), end_vars[i] == friend["avail_start"]))

# For any two meetings that are both scheduled, add a non‐overlap constraint.
# That is, one meeting must finish plus the travel time to the next meeting before the other can start.
for i in range(n):
    for j in range(i + 1, n):
        loc_i = friends[i]["location"]
        loc_j = friends[j]["location"]
        # Get travel time from i to j and from j to i (if missing, use a large default).
        t_ij = travel_times.get((loc_i, loc_j), 1000)
        t_ji = travel_times.get((loc_j, loc_i), 1000)
        opt.add(Implies(And(decided[i], decided[j]),
                        Or(start_vars[j] >= end_vars[i] + t_ij,
                           start_vars[i] >= end_vars[j] + t_ji)))

# Our objective is to maximize the number of meetings scheduled.
opt.maximize(Sum([If(decided[i], 1, 0) for i in range(n)]))

# Solve the optimization problem.
if opt.check() == sat:
    model = opt.model()
    scheduled = []
    for i, friend in enumerate(friends):
        if is_true(model.evaluate(decided[i])):
            s = model.evaluate(start_vars[i]).as_long()
            e = model.evaluate(end_vars[i]).as_long()
            scheduled.append((s, e, friend["name"]))
    # Sort the meetings by start time.
    scheduled.sort(key=lambda x: x[0])
    
    def minutes_to_time(m):
        hh = m // 60
        mm = m % 60
        return f"{hh:02d}:{mm:02d}"
    
    itinerary = []
    for s, e, name in scheduled:
        itinerary.append({
            "action": "meet",
            "person": name,
            "start_time": minutes_to_time(s),
            "end_time": minutes_to_time(e)
        })
    
    result = {"itinerary": itinerary}
    print("SOLUTION:")
    print(json.dumps(result, indent=2))
else:
    print("No solution found")