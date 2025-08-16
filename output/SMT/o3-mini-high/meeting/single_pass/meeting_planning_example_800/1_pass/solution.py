from z3 import Int, Bool, Optimize, If, And, Or, Implies, sat
import json

# Helper function to convert minutes-since-midnight into "HH:MM" string.
def minutes_to_timestr(m):
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Friend data.
# Times are in minutes from midnight.
# For example, 9:00 AM = 540.
friends = [
    {"name": "Kimberly", "location": "North Beach", "avail_start": 420, "avail_end": 630, "duration": 15},       # 07:00-10:30, 15 min
    {"name": "Brian",     "location": "Fisherman's Wharf", "avail_start": 570, "avail_end": 930, "duration": 45},   # 09:30-15:30, 45 min
    {"name": "Kenneth",   "location": "Nob Hill", "avail_start": 735, "avail_end": 1035, "duration": 105},          # 12:15-17:15, 105 min
    {"name": "Joseph",    "location": "Embarcadero", "avail_start": 930, "avail_end": 1170, "duration": 75},         # 15:30-19:30, 75 min
    {"name": "Betty",     "location": "Haight-Ashbury", "avail_start": 1140, "avail_end": 1230, "duration": 90},      # 19:00-20:30, 90 min
    {"name": "Melissa",   "location": "The Castro", "avail_start": 1215, "avail_end": 1275, "duration": 30},          # 20:15-21:15, 30 min
    {"name": "Barbara",   "location": "Alamo Square", "avail_start": 1245, "avail_end": 1305, "duration": 15},        # 20:45-21:45, 15 min
    {"name": "Joshua",    "location": "Presidio", "avail_start": 990, "avail_end": 1095, "duration": 105},            # 16:30-18:15, 105 min
    {"name": "Steven",    "location": "Mission District", "avail_start": 1170, "avail_end": 1260, "duration": 90}      # 19:30-21:00, 90 min
]

# Travel times in minutes between locations.
# Note: these are directed travel times.
travel = {
    ("Union Square", "The Castro"): 17,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Embarcadero"): 11,
    ("Union Square", "Alamo Square"): 15,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Presidio"): 24,
    ("Union Square", "Fisherman's Wharf"): 15,
    ("Union Square", "Mission District"): 14,
    ("Union Square", "Haight-Ashbury"): 18,

    ("The Castro", "Union Square"): 19,
    ("The Castro", "North Beach"): 20,
    ("The Castro", "Embarcadero"): 22,
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Presidio"): 20,
    ("The Castro", "Fisherman's Wharf"): 24,
    ("The Castro", "Mission District"): 7,
    ("The Castro", "Haight-Ashbury"): 6,

    ("North Beach", "Union Square"): 7,
    ("North Beach", "The Castro"): 23,
    ("North Beach", "Embarcadero"): 6,
    ("North Beach", "Alamo Square"): 16,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Mission District"): 18,
    ("North Beach", "Haight-Ashbury"): 18,

    ("Embarcadero", "Union Square"): 10,
    ("Embarcadero", "The Castro"): 25,
    ("Embarcadero", "North Beach"): 5,
    ("Embarcadero", "Alamo Square"): 19,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Embarcadero", "Mission District"): 20,
    ("Embarcadero", "Haight-Ashbury"): 21,

    ("Alamo Square", "Union Square"): 14,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Embarcadero"): 16,
    ("Alamo Square", "Nob Hill"): 11,
    ("Alamo Square", "Presidio"): 17,
    ("Alamo Square", "Fisherman's Wharf"): 19,
    ("Alamo Square", "Mission District"): 10,
    ("Alamo Square", "Haight-Ashbury"): 5,

    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Embarcadero"): 9,
    ("Nob Hill", "Alamo Square"): 11,
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "Fisherman's Wharf"): 10,
    ("Nob Hill", "Mission District"): 13,
    ("Nob Hill", "Haight-Ashbury"): 13,

    ("Presidio", "Union Square"): 22,
    ("Presidio", "The Castro"): 21,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Alamo Square"): 19,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Mission District"): 26,
    ("Presidio", "Haight-Ashbury"): 15,

    ("Fisherman's Wharf", "Union Square"): 13,
    ("Fisherman's Wharf", "The Castro"): 27,
    ("Fisherman's Wharf", "North Beach"): 6,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "Alamo Square"): 21,
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Fisherman's Wharf", "Haight-Ashbury"): 22,

    ("Mission District", "Union Square"): 15,
    ("Mission District", "The Castro"): 7,
    ("Mission District", "North Beach"): 17,
    ("Mission District", "Embarcadero"): 19,
    ("Mission District", "Alamo Square"): 11,
    ("Mission District", "Nob Hill"): 12,
    ("Mission District", "Presidio"): 25,
    ("Mission District", "Fisherman's Wharf"): 22,
    ("Mission District", "Haight-Ashbury"): 12,

    ("Haight-Ashbury", "Union Square"): 19,
    ("Haight-Ashbury", "The Castro"): 6,
    ("Haight-Ashbury", "North Beach"): 19,
    ("Haight-Ashbury", "Embarcadero"): 20,
    ("Haight-Ashbury", "Alamo Square"): 5,
    ("Haight-Ashbury", "Nob Hill"): 15,
    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Haight-Ashbury", "Mission District"): 11,
}

# Create Z3 optimization instance.
opt = Optimize()

n = len(friends)

# Decision variables: s[i] is the meeting start time and chosen[i] is a Bool indicating if friend i is visited.
s_vars = [Int("s_" + friend["name"]) for friend in friends]
chosen_vars = [Bool("chosen_" + friend["name"]) for friend in friends]

# Our current starting time is at Union Square at 9:00 AM = 540.
start_time = 540

# Add constraints for each friend appointment.
for i, friend in enumerate(friends):
    # If meeting is scheduled then its start time must be within the friend's availability window,
    # and the meeting must finish by the end of availability.
    opt.add(Implies(chosen_vars[i], s_vars[i] >= friend["avail_start"]))
    opt.add(Implies(chosen_vars[i], s_vars[i] + friend["duration"] <= friend["avail_end"]))
    # Also, if scheduled, ensure that the meeting cannot start before you could get there directly from Union Square.
    key = ("Union Square", friend["location"])
    if key in travel:
        opt.add(Implies(chosen_vars[i], s_vars[i] >= start_time + travel[key]))
    else:
        # If for some reason there's no travel time listed, assume no extra constraint.
        opt.add(Implies(chosen_vars[i], s_vars[i] >= start_time))

# Add disjunctive constraints for every pair of scheduled meetings.
for i in range(n):
    for j in range(i+1, n):
        # If both meetings are scheduled, then either i comes before j (including travel time)
        # or j comes before i.
        key_ij = (friends[i]["location"], friends[j]["location"])
        key_ji = (friends[j]["location"], friends[i]["location"])
        t_ij = travel.get(key_ij, 0)
        t_ji = travel.get(key_ji, 0)
        opt.add(Implies(And(chosen_vars[i], chosen_vars[j]),
                        Or(s_vars[i] + friends[i]["duration"] + t_ij <= s_vars[j],
                           s_vars[j] + friends[j]["duration"] + t_ji <= s_vars[i])))

# Set the objective: maximize the number of friends met.
obj = sum([If(chosen_vars[i], 1, 0) for i in range(n)])
opt.maximize(obj)

# Now check for a solution.
if opt.check() == sat:
    model = opt.model()
    scheduled = []
    for i, friend in enumerate(friends):
        if model.evaluate(chosen_vars[i]):
            start_val = model.evaluate(s_vars[i]).as_long()
            end_val = start_val + friend["duration"]
            scheduled.append({
                "person": friend["name"],
                "start": start_val,
                "end": end_val,
                "location": friend["location"]
            })
    # Sort scheduled meetings by start time.
    scheduled.sort(key=lambda x: x["start"])
    
    # Build itinerary list in required JSON format.
    itinerary = []
    for appt in scheduled:
        itinerary.append({
            "action": "meet",
            "person": appt["person"],
            "start_time": minutes_to_timestr(appt["start"]),
            "end_time": minutes_to_timestr(appt["end"])
        })
    
    # Output the JSON dictionary
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))
else:
    print("No valid schedule found.")