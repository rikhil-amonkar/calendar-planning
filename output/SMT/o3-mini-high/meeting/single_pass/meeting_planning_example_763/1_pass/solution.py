from z3 import *
import json

# Define the friends with their meeting location, availability window (in minutes after midnight) and minimum meeting duration.
# Times: 9:00 = 540, 13:45 = 825, 15:15 = 915, 15:00 = 900, 17:00 = 1020, 17:30 = 1050, 18:45 = 1125, 21:00 = 1260, etc.
friends = [
    {"name": "Richard", "location": "Embarcadero", "avail_start": 915, "avail_end": 1125, "duration": 90},
    {"name": "Mark", "location": "Pacific Heights", "avail_start": 900, "avail_end": 1020, "duration": 45},
    {"name": "Matthew", "location": "Russian Hill", "avail_start": 1050, "avail_end": 1260, "duration": 90},
    {"name": "Rebecca", "location": "Haight-Ashbury", "avail_start": 885, "avail_end": 1080, "duration": 60},
    {"name": "Melissa", "location": "Golden Gate Park", "avail_start": 825, "avail_end": 1050, "duration": 90},
    {"name": "Margaret", "location": "Fisherman's Wharf", "avail_start": 885, "avail_end": 1215, "duration": 15},
    {"name": "Emily", "location": "Sunset District", "avail_start": 945, "avail_end": 1020, "duration": 45},
    {"name": "George", "location": "The Castro", "avail_start": 840, "avail_end": 975, "duration": 75}
]

# Define travel distances (in minutes) between neighborhoods.
# Note that travel times are not symmetric.
travel_times = {
  ("Chinatown", "Embarcadero"): 5,
  ("Chinatown", "Pacific Heights"): 10,
  ("Chinatown", "Russian Hill"): 7,
  ("Chinatown", "Haight-Ashbury"): 19,
  ("Chinatown", "Golden Gate Park"): 23,
  ("Chinatown", "Fisherman's Wharf"): 8,
  ("Chinatown", "Sunset District"): 29,
  ("Chinatown", "The Castro"): 22,

  ("Embarcadero", "Chinatown"): 7,
  ("Embarcadero", "Pacific Heights"): 11,
  ("Embarcadero", "Russian Hill"): 8,
  ("Embarcadero", "Haight-Ashbury"): 21,
  ("Embarcadero", "Golden Gate Park"): 25,
  ("Embarcadero", "Fisherman's Wharf"): 6,
  ("Embarcadero", "Sunset District"): 30,
  ("Embarcadero", "The Castro"): 25,

  ("Pacific Heights", "Chinatown"): 11,
  ("Pacific Heights", "Embarcadero"): 10,
  ("Pacific Heights", "Russian Hill"): 7,
  ("Pacific Heights", "Haight-Ashbury"): 11,
  ("Pacific Heights", "Golden Gate Park"): 15,
  ("Pacific Heights", "Fisherman's Wharf"): 13,
  ("Pacific Heights", "Sunset District"): 21,
  ("Pacific Heights", "The Castro"): 16,

  ("Russian Hill", "Chinatown"): 9,
  ("Russian Hill", "Embarcadero"): 8,
  ("Russian Hill", "Pacific Heights"): 7,
  ("Russian Hill", "Haight-Ashbury"): 17,
  ("Russian Hill", "Golden Gate Park"): 21,
  ("Russian Hill", "Fisherman's Wharf"): 7,
  ("Russian Hill", "Sunset District"): 23,
  ("Russian Hill", "The Castro"): 21,

  ("Haight-Ashbury", "Chinatown"): 19,
  ("Haight-Ashbury", "Embarcadero"): 20,
  ("Haight-Ashbury", "Pacific Heights"): 12,
  ("Haight-Ashbury", "Russian Hill"): 17,
  ("Haight-Ashbury", "Golden Gate Park"): 7,
  ("Haight-Ashbury", "Fisherman's Wharf"): 23,
  ("Haight-Ashbury", "Sunset District"): 15,
  ("Haight-Ashbury", "The Castro"): 6,

  ("Golden Gate Park", "Chinatown"): 23,
  ("Golden Gate Park", "Embarcadero"): 25,
  ("Golden Gate Park", "Pacific Heights"): 16,
  ("Golden Gate Park", "Russian Hill"): 19,
  ("Golden Gate Park", "Haight-Ashbury"): 7,
  ("Golden Gate Park", "Fisherman's Wharf"): 24,
  ("Golden Gate Park", "Sunset District"): 10,
  ("Golden Gate Park", "The Castro"): 13,

  ("Fisherman's Wharf", "Chinatown"): 12,
  ("Fisherman's Wharf", "Embarcadero"): 8,
  ("Fisherman's Wharf", "Pacific Heights"): 12,
  ("Fisherman's Wharf", "Russian Hill"): 7,
  ("Fisherman's Wharf", "Haight-Ashbury"): 22,
  ("Fisherman's Wharf", "Golden Gate Park"): 25,
  ("Fisherman's Wharf", "Sunset District"): 27,
  ("Fisherman's Wharf", "The Castro"): 27,

  ("Sunset District", "Chinatown"): 30,
  ("Sunset District", "Embarcadero"): 30,
  ("Sunset District", "Pacific Heights"): 21,
  ("Sunset District", "Russian Hill"): 24,
  ("Sunset District", "Haight-Ashbury"): 15,
  ("Sunset District", "Golden Gate Park"): 11,
  ("Sunset District", "Fisherman's Wharf"): 29,
  ("Sunset District", "The Castro"): 17,

  ("The Castro", "Chinatown"): 22,
  ("The Castro", "Embarcadero"): 22,
  ("The Castro", "Pacific Heights"): 16,
  ("The Castro", "Russian Hill"): 18,
  ("The Castro", "Haight-Ashbury"): 6,
  ("The Castro", "Golden Gate Park"): 11,
  ("The Castro", "Fisherman's Wharf"): 24,
  ("The Castro", "Sunset District"): 17
}

def travel_time(src, dst):
    # Return the travel time between two locations.
    return travel_times.get((src, dst), 1000)

# Create an Optimize solver instance.
opt = Optimize()

n = len(friends)
# For each friend we create an integer variable for the meeting start time (in minutes after midnight)
S = [Int(f"S_{i}") for i in range(n)]
# And a Boolean variable indicating whether we meet that friend.
meet_vars = [Bool(f"meet_{i}") for i in range(n)]

# For each friend, if we decide to meet them, the meeting start must be at or after:
#   - their availability start time, and
#   - the time needed to get there from Chinatown (starting at 9:00, i.e. 540 minutes)
for i, f in enumerate(friends):
    lower_bound = max(f["avail_start"], 540 + travel_time("Chinatown", f["location"]))
    opt.add(Implies(meet_vars[i], S[i] >= lower_bound))
    # Also the meeting must finish before the friend’s availability ends.
    opt.add(Implies(meet_vars[i], S[i] + f["duration"] <= f["avail_end"]))

# For every pair of meetings (if both are selected), we add a disjunctive constraint.
# Either meeting i happens entirely before meeting j (including the travel time from i’s location to j’s)
# or meeting j happens before meeting i.
for i in range(n):
    for j in range(i+1, n):
        f_i = friends[i]
        f_j = friends[j]
        order_constraint = Or(
            S[i] + f_i["duration"] + travel_time(f_i["location"], f_j["location"]) <= S[j],
            S[j] + f_j["duration"] + travel_time(f_j["location"], f_i["location"]) <= S[i]
        )
        opt.add(Implies(And(meet_vars[i], meet_vars[j]), order_constraint))

# Our goal is to maximize the number of meetings (i.e. friends met)
opt.maximize(Sum([If(m, 1, 0) for m in meet_vars]))

# Solve the scheduling problem.
if opt.check() == sat:
    model = opt.model()
    scheduled = []
    for i, f in enumerate(friends):
        if is_true(model[meet_vars[i]]):
            start = model[S[i]].as_long()
            end = start + f["duration"]
            scheduled.append((start, {
                "action": "meet",
                "person": f["name"],
                "start_time": f"{start//60:02d}:{start % 60:02d}",
                "end_time": f"{end//60:02d}:{end % 60:02d}"
            }))
    # Sort meetings by start time.
    scheduled.sort(key=lambda x: x[0])
    itinerary = [entry for _, entry in scheduled]
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))
else:
    print("No solution found")