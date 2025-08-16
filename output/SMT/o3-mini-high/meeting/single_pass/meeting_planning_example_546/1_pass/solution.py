from z3 import *
import json

# Helper function: converts minutes since midnight to "HH:MM" format.
def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

# Data for each friend: name, meeting location, available interval (in minutes since midnight) and minimum meeting duration.
# Times:
#   8:00  -> 480, 9:00 -> 540, 9:15 -> 555, 11:30 -> 690, 12:00 -> 720, 15:15 -> 915,
#   16:30 -> 990, 16:45 -> 1005, 20:15 -> 1215, 21:15 -> 1275, 21:30 -> 1290, 22:00 -> 1320
persons = [
    {"name": "Nancy",   "loc": "Pacific Heights",    "avail_start": 480,  "avail_end": 690,  "dur": 90},
    {"name": "Lisa",    "loc": "Union Square",         "avail_start": 540,  "avail_end": 990,  "dur": 45},
    {"name": "Joshua",  "loc": "Financial District",   "avail_start": 720,  "avail_end": 915,  "dur": 15},
    {"name": "Andrew",  "loc": "Nob Hill",             "avail_start": 690,  "avail_end": 1215, "dur": 60},
    {"name": "John",    "loc": "Bayview",              "avail_start": 1005, "avail_end": 1290, "dur": 75},
    {"name": "Kenneth", "loc": "Richmond District",    "avail_start": 1275, "avail_end": 1320, "dur": 30}
]

# Travel times between locations (in minutes) as given.
travel_times = {
    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "Union Square"): 10,
    ("Embarcadero", "Financial District"): 5,
    ("Embarcadero", "Pacific Heights"): 11,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "Bayview"): 21,

    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "Union Square"): 21,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "Pacific Heights"): 10,
    ("Richmond District", "Nob Hill"): 17,
    ("Richmond District", "Bayview"): 26,

    ("Union Square", "Embarcadero"): 11,
    ("Union Square", "Richmond District"): 20,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Bayview"): 15,

    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "Union Square"): 9,
    ("Financial District", "Pacific Heights"): 13,
    ("Financial District", "Nob Hill"): 8,
    ("Financial District", "Bayview"): 19,

    ("Pacific Heights", "Embarcadero"): 10,
    ("Pacific Heights", "Richmond District"): 12,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Financial District"): 13,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Bayview"): 22,

    ("Nob Hill", "Embarcadero"): 9,
    ("Nob Hill", "Richmond District"): 14,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "Financial District"): 9,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "Bayview"): 19,

    ("Bayview", "Embarcadero"): 19,
    ("Bayview", "Richmond District"): 25,
    ("Bayview", "Union Square"): 17,
    ("Bayview", "Financial District"): 19,
    ("Bayview", "Pacific Heights"): 23,
    ("Bayview", "Nob Hill"): 20
}

# Starting point information.
start_location = "Embarcadero"
arrival_time = 540  # You arrive at Embarcadero at 09:00 (540 minutes after midnight).

# We choose an ordering of meetings that respects time‐windows and minimizes waiting:
# Order: Nancy -> Lisa -> Joshua -> Andrew -> John -> Kenneth
order = ["Nancy", "Lisa", "Joshua", "Andrew", "John", "Kenneth"]

# Create a Z3 solver instance.
solver = Solver()

# Create Z3 integer variables for each meeting's start time.
start_vars = {}
for p in persons:
    start_vars[p["name"]] = Int(f'start_{p["name"]}')

# Add basic constraints for each meeting: meeting must occur within the available window
# and last at least the minimum required duration.
for p in persons:
    name = p["name"]
    avail_start = p["avail_start"]
    avail_end = p["avail_end"]
    dur = p["dur"]
    solver.add(start_vars[name] >= avail_start)
    solver.add(start_vars[name] + dur <= avail_end)

# Helper: Given a friend's name, return the corresponding dictionary from persons.
def get_person(name):
    for p in persons:
        if p["name"] == name:
            return p
    return None

# Add travel constraints for the ordered sequence of meetings.
# For the first meeting, you must travel from the Embarcadero to the friend's location.
first = order[0]
first_person = get_person(first)
solver.add(start_vars[first] >= arrival_time + travel_times[(start_location, first_person["loc"])])

# For each consecutive pair, ensure that you finish the previous meeting and travel to the next.
for i in range(1, len(order)):
    prev_name = order[i - 1]
    curr_name = order[i]
    prev_person = get_person(prev_name)
    curr_person = get_person(curr_name)
    travel = travel_times[(prev_person["loc"], curr_person["loc"])]
    # The next meeting cannot start until after the previous meeting ends plus travel time.
    solver.add(start_vars[curr_name] >= start_vars[prev_name] + prev_person["dur"] + travel)

# Solve for a valid schedule.
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    # Build the itinerary list in the order determined.
    for name in order:
        p = get_person(name)
        start_val = model[start_vars[name]].as_long()
        end_val = start_val + p["dur"]
        itinerary.append({
            "action": "meet",
            "person": name,
            "start_time": minutes_to_time(start_val),
            "end_time": minutes_to_time(end_val)
        })
    output = {"itinerary": itinerary}
    print("SOLUTION:")
    print(json.dumps(output, indent=4))
else:
    print("No solution found")