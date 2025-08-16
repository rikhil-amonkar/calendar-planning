from z3 import *
import json

# Helper function: convert minutes from midnight to HH:MM string.
def to_time(t):
    hours = t // 60
    minutes = t % 60
    return f"{hours:02d}:{minutes:02d}"

# Travel times dictionary as given.
# Keys are tuples (from, to)
travel_times = {
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Fisherman's Wharf"): 10,
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "Embarcadero"): 14,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "North Beach"): 11,
    ("Marina District", "Presidio"): 10,
    
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "Union Square"): 21,
    ("Richmond District", "Nob Hill"): 17,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "North Beach"): 17,
    ("Richmond District", "Presidio"): 7,
    
    ("Union Square", "Marina District"): 18,
    ("Union Square", "Richmond District"): 20,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Fisherman's Wharf"): 15,
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Embarcadero"): 11,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Presidio"): 24,
    
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "Richmond District"): 14,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "Fisherman's Wharf"): 10,
    ("Nob Hill", "Golden Gate Park"): 17,
    ("Nob Hill", "Embarcadero"): 9,
    ("Nob Hill", "Financial District"): 9,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Presidio"): 17,
    
    ("Fisherman's Wharf", "Marina District"): 9,
    ("Fisherman's Wharf", "Richmond District"): 18,
    ("Fisherman's Wharf", "Union Square"): 13,
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Fisherman's Wharf", "North Beach"): 6,
    ("Fisherman's Wharf", "Presidio"): 17,
    
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Nob Hill"): 20,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "North Beach"): 23,
    ("Golden Gate Park", "Presidio"): 11,
    
    ("Embarcadero", "Marina District"): 12,
    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "Union Square"): 10,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Financial District"): 5,
    ("Embarcadero", "North Beach"): 5,
    ("Embarcadero", "Presidio"): 20,
    
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "Union Square"): 9,
    ("Financial District", "Nob Hill"): 9,
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Financial District", "Golden Gate Park"): 26,
    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "North Beach"): 7,
    ("Financial District", "Presidio"): 22,
    
    ("North Beach", "Marina District"): 9,
    ("North Beach", "Richmond District"): 18,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Embarcadero"): 6,
    ("North Beach", "Financial District"): 8,
    ("North Beach", "Presidio"): 17,
    
    ("Presidio", "Marina District"): 11,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Union Square"): 22,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "North Beach"): 18
}

# List of friends with their meeting details.
# Times are in minutes after midnight.
# Marina District is the starting point at 9:00 (540 minutes).
# Each friend has an availability window [earliest, latest]
# and a minimum meeting duration.
friends = [
    {"name": "Sandra", "location": "North Beach", "earliest": 600,  "latest": 750,  "duration": 15},
    {"name": "William", "location": "Union Square", "earliest": 645,  "latest": 1050, "duration": 45},
    {"name": "Carol", "location": "Financial District", "earliest": 705,  "latest": 975,  "duration": 60},
    {"name": "Elizabeth", "location": "Nob Hill", "earliest": 735,  "latest": 900,  "duration": 105},
    {"name": "Joseph", "location": "Fisherman's Wharf", "earliest": 765,  "latest": 840,  "duration": 75},
    {"name": "Anthony", "location": "Golden Gate Park", "earliest": 780,  "latest": 1230, "duration": 75},
    {"name": "Stephanie", "location": "Richmond District", "earliest": 975,  "latest": 1290, "duration": 75},
    {"name": "Barbara", "location": "Embarcadero", "earliest": 1155, "latest": 1230, "duration": 75},
    {"name": "Kenneth", "location": "Presidio", "earliest": 1275, "latest": 1335, "duration": 45},
]
n = len(friends)

# Create Z3 solver using Optimize so we can maximize number of meetings.
opt = Optimize()

# Variables: for each friend i we decide whether to meet (meet[i] = True),
# the start time start[i] (in minutes) and end time end[i] (in minutes)
meet_vars = [Bool(f"meet_{i}") for i in range(n)]
start_vars = [Int(f"start_{i}") for i in range(n)]
end_vars   = [Int(f"end_{i}")   for i in range(n)]

# For every unordered pair i<j of friends, we introduce a Boolean variable 
# order_{i,j} meaning "if both meetings occur then friend i is scheduled before friend j".
order_vars = {}
for i in range(n):
    for j in range(i+1, n):
        order_vars[(i,j)] = Bool(f"order_{i}_{j}")

# Add constraints for each friend that if the meeting is scheduled, 
# then the meeting must lie in the available time window and be exactly the minimum duration.
for i, f in enumerate(friends):
    # If scheduled then start time >= friend available earliest
    # AND meeting must finish (start + duration) by friend’s latest.
    # Also enforce that we cannot begin before we could travel from Marina.
    opt.add(Implies(meet_vars[i],
                    And(start_vars[i] >= f["earliest"],
                        start_vars[i] <= f["latest"] - f["duration"],
                        start_vars[i] >= 540 + travel_times[("Marina District", f["location"])],
                        start_vars[i] + f["duration"] <= f["latest"])))
    # Fix meeting duration to be exactly the minimum (so as to “minimize” use of time)
    opt.add(Implies(meet_vars[i],
                    end_vars[i] == start_vars[i] + f["duration"]))

# Disjunctive (ordering) constraints:
# For every pair i < j, if both meetings are scheduled, then either i comes before j or vice‐versa.
# And the travel time between meeting locations must be respected.
for i in range(n):
    for j in range(i+1, n):
        f_i = friends[i]
        f_j = friends[j]
        # If both meetings occur, then order_vars[(i,j)] can be used to decide the order.
        # If order_vars[(i,j)] is True then i is before j so start_j >= end_i + travel_time(i->j).
        # Otherwise j is before i so start_i >= end_j + travel_time(j->i).
        travel_ij = travel_times[(f_i["location"], f_j["location"])]
        travel_ji = travel_times[(f_j["location"], f_i["location"])]
        opt.add(Implies(And(meet_vars[i], meet_vars[j], order_vars[(i,j)]),
                        start_vars[j] >= end_vars[i] + travel_ij))
        opt.add(Implies(And(meet_vars[i], meet_vars[j], Not(order_vars[(i,j)])),
                        start_vars[i] >= end_vars[j] + travel_ji))
        # (No need to force an "either or" explicitly because the Boolean variable takes a value.)

# Optional: add transitivity constraints.
# For all distinct i, j, k with i < j < k, if meetings occur and i precedes j and j precedes k,
# then i must precede k.
for i in range(n):
    for j in range(i+1, n):
        for k in range(j+1, n):
            opt.add(Implies(And(meet_vars[i], meet_vars[j], meet_vars[k],
                                order_vars[(i, j)], order_vars[(j, k)]),
                            order_vars[(i, k)]))

# We want to maximize the number of friends you can meet.
opt.maximize(Sum([If(meet_vars[i], 1, 0) for i in range(n)]))

# Check and get the model.
if opt.check() == sat:
    model = opt.model()
    # Extract scheduled meetings together with start and end times.
    schedule = []
    for i in range(n):
        if is_true(model.evaluate(meet_vars[i])):
            st = model.evaluate(start_vars[i]).as_long()
            en = model.evaluate(end_vars[i]).as_long()
            schedule.append({
                "person": friends[i]["name"],
                "start": st,
                "end": en,
                "location": friends[i]["location"]
            })
    # Sort the scheduled meetings by start time.
    schedule.sort(key=lambda x: x["start"])
    
    # Build the itinerary in the required JSON format.
    itinerary = []
    for meeting in schedule:
        itinerary.append({
            "action": "meet",
            "person": meeting["person"],
            "start_time": to_time(meeting["start"]),
            "end_time": to_time(meeting["end"])
        })
    
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))
else:
    print("No solution found.")