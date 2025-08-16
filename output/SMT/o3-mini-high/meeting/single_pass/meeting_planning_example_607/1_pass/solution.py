from z3 import Int, Solver, Or, sat
import json

# Helper function: convert minutes after midnight into "HH:MM" string.
def minutes_to_str(m):
    h = m // 60
    min_ = m % 60
    return f"{h:02d}:{min_:02d}"

# Data for friends:
# Each entry: (person, location, avail_start, avail_end, min_duration)
# Times are in minutes after midnight.
friends = [
    ("Matthew", "Richmond District", 450, 915, 15),      # 07:30 -> 15:15, 15 min
    ("Michelle", "Marina District", 630, 1125, 75),         # 10:30 -> 18:45, 75 min
    ("Stephanie", "Union Square", 645, 855, 30),            # 10:45 -> 14:15, 30 min
    ("Carol", "North Beach", 720, 1020, 90),                # 12:00 -> 17:00, 90 min
    ("Jessica", "The Castro", 945, 1170, 60),               # 15:45 -> 19:30, 60 min
    ("Linda", "Golden Gate Park", 645, 1320, 90),           # 10:45 -> 22:00, 90 min
    ("Karen", "Russian Hill", 1245, 1305, 60)               # 20:45 -> 21:45, 60 min
]

# Travel times in minutes between locations.
# The keys are tuples (from_location, to_location).
travel_times = {
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "Richmond District"): 12,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "North Beach"): 29,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Golden Gate Park"): 11,

    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Richmond District"): 14,
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "North Beach"): 5,
    ("Russian Hill", "Union Square"): 11,
    ("Russian Hill", "Golden Gate Park"): 21,

    ("The Castro", "Sunset District"): 17,
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "Richmond District"): 16,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "North Beach"): 20,
    ("The Castro", "Union Square"): 19,
    ("The Castro", "Golden Gate Park"): 11,

    ("Richmond District", "Sunset District"): 11,
    ("Richmond District", "Russian Hill"): 13,
    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "North Beach"): 17,
    ("Richmond District", "Union Square"): 21,
    ("Richmond District", "Golden Gate Park"): 9,

    ("Marina District", "Sunset District"): 19,
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "North Beach"): 11,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Golden Gate Park"): 18,

    ("North Beach", "Sunset District"): 27,
    ("North Beach", "Russian Hill"): 4,
    ("North Beach", "The Castro"): 22,
    ("North Beach", "Richmond District"): 18,
    ("North Beach", "Marina District"): 9,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Golden Gate Park"): 22,

    ("Union Square", "Sunset District"): 26,
    ("Union Square", "Russian Hill"): 13,
    ("Union Square", "The Castro"): 19,
    ("Union Square", "Richmond District"): 20,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Golden Gate Park"): 22,

    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "North Beach"): 24,
    ("Golden Gate Park", "Union Square"): 22,
}

# Arrival details:
arrival_time = 540  # 9:00 AM in minutes after midnight
start_location = "Sunset District"

# Create Z3 solver.
solver = Solver()

# Create variables for each friend: meeting start time s and meeting end time e.
s_vars = {}
e_vars = {}

for person, loc, a_start, a_end, dur in friends:
    # s_vars and e_vars represent the start time and end time (in minutes) of the meeting.
    s = Int(f"s_{person.replace(' ', '_')}")
    e = Int(f"e_{person.replace(' ', '_')}")
    s_vars[person] = s
    e_vars[person] = e
    # Meeting must lie within the available window.
    solver.add(s >= a_start)
    solver.add(s <= a_end - dur)  # so that meeting can last at least the min duration
    solver.add(e <= a_end)
    # Force meeting duration to be exactly the minimum required (for a compact schedule).
    solver.add(e == s + dur)
    # Also, the meeting cannot begin before you can get there from the Sunset District.
    key = (start_location, loc)
    if key in travel_times:
        solver.add(s >= arrival_time + travel_times[key])
    else:
        # If no travel info is provided, assume 0.
        solver.add(s >= arrival_time)

# For convenience, build a lookup for friend's location and duration.
friend_info = {person: {"loc": loc, "dur": dur} for person, loc, a_start, a_end, dur in friends}

# Non-overlap constraints: for every pair of meetings, one must finish (with travel time) before the other starts.
persons = [person for person, _, _, _, _ in friends]
n = len(persons)
for i in range(n):
    for j in range(i+1, n):
        person_i = persons[i]
        person_j = persons[j]
        loc_i = friend_info[person_i]["loc"]
        loc_j = friend_info[person_j]["loc"]
        dur_i = friend_info[person_i]["dur"]
        dur_j = friend_info[person_j]["dur"]
        # Travel time from i to j:
        travel_ij = travel_times.get((loc_i, loc_j), 0)
        travel_ji = travel_times.get((loc_j, loc_i), 0)
        # Add disjunctive ordering constraint:
        solver.add(Or(s_vars[person_i] + dur_i + travel_ij <= s_vars[person_j],
                      s_vars[person_j] + dur_j + travel_ji <= s_vars[person_i]))

# Check for a solution.
if solver.check() == sat:
    m = solver.model()
    # Build itinerary: list of meeting entries
    itinerary = []
    # Gather (person, start, end) from model.
    schedule = []
    for person in persons:
        s_time = m[s_vars[person]].as_long()
        e_time = m[e_vars[person]].as_long()
        schedule.append((person, s_time, e_time))
    # Sort meetings by start time.
    schedule.sort(key=lambda x: x[1])
    for person, s_time, e_time in schedule:
        itinerary.append({
            "action": "meet",
            "person": person,
            "start_time": minutes_to_str(s_time),
            "end_time": minutes_to_str(e_time)
        })
    # Output the itinerary in JSON format.
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))
else:
    print("No solution found")