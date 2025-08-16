from z3 import *
import json

# Helper: convert minutes since midnight into HH:MM string.
def format_time(t):
    hours = t // 60
    minutes = t % 60
    return f"{hours:02d}:{minutes:02d}"

# Define the friend meeting data:
# Times are given in minutes after midnight.
friends = [
    {"name": "Jason",     "location": "Chinatown",           "avail_start": 8*60+15,   "avail_end": 11*60+45,  "duration": 75},
    {"name": "Mark",      "location": "Marina District",     "avail_start": 10*60+15,  "avail_end": 13*60,     "duration": 75},
    {"name": "Kimberly",  "location": "Embarcadero",         "avail_start": 9*60+45,   "avail_end": 19*60+30,  "duration": 75},
    {"name": "Jessica",   "location": "Nob Hill",            "avail_start": 13*60+45,  "avail_end": 21*60,     "duration": 90},
    {"name": "Stephanie", "location": "Union Square",        "avail_start": 14*60+45,  "avail_end": 18*60+45,  "duration": 105},
    {"name": "Brian",     "location": "Russian Hill",        "avail_start": 15*60+30,  "avail_end": 21*60+45,  "duration": 60},
    {"name": "Steven",    "location": "Financial District",  "avail_start": 7*60+15,   "avail_end": 21*60+15,  "duration": 60},
    {"name": "Kenneth",   "location": "North Beach",         "avail_start": 9*60+45,   "avail_end": 21*60,     "duration": 30},
    {"name": "Karen",     "location": "Haight-Ashbury",      "avail_start": 21*60,     "avail_end": 21*60+45,  "duration": 45}
]

N = len(friends)

# The travel time dictionary.
# Keys are pairs (from, to) and values are travel times (in minutes).
travel = {
    # From Presidio to others:
    ("Presidio", "Haight-Ashbury"): 15,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Union Square"): 22,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "Marina District"): 11,
    # And symmetric:
    ("Haight-Ashbury", "Presidio"): 15,
    
    # Haight-Ashbury row:
    ("Haight-Ashbury", "Nob Hill"): 15,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "North Beach"): 19,
    ("Haight-Ashbury", "Chinatown"): 19,
    ("Haight-Ashbury", "Union Square"): 19,
    ("Haight-Ashbury", "Embarcadero"): 20,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Haight-Ashbury", "Marina District"): 17,
    
    # Nob Hill row:
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "Haight-Ashbury"): 13,
    ("Nob Hill", "Russian Hill"): 5,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "Embarcadero"): 9,
    ("Nob Hill", "Financial District"): 9,
    ("Nob Hill", "Marina District"): 11,
    
    # Russian Hill row:
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "Nob Hill"): 5,
    ("Russian Hill", "North Beach"): 5,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "Union Square"): 10,
    ("Russian Hill", "Embarcadero"): 8,
    ("Russian Hill", "Financial District"): 11,
    ("Russian Hill", "Marina District"): 7,
    
    # North Beach row:
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Haight-Ashbury"): 18,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Russian Hill"): 4,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Embarcadero"): 6,
    ("North Beach", "Financial District"): 8,
    ("North Beach", "Marina District"): 9,
    
    # Chinatown row:
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Haight-Ashbury"): 19,
    ("Chinatown", "Nob Hill"): 9,
    ("Chinatown", "Russian Hill"): 7,
    ("Chinatown", "North Beach"): 3,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Embarcadero"): 5,
    ("Chinatown", "Financial District"): 5,
    ("Chinatown", "Marina District"): 12,
    
    # Union Square row:
    ("Union Square", "Presidio"): 24,
    ("Union Square", "Haight-Ashbury"): 18,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Russian Hill"): 13,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Embarcadero"): 11,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Marina District"): 18,
    
    # Embarcadero row:
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Haight-Ashbury"): 21,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "Russian Hill"): 8,
    ("Embarcadero", "North Beach"): 5,
    ("Embarcadero", "Chinatown"): 7,
    ("Embarcadero", "Union Square"): 10,
    ("Embarcadero", "Financial District"): 5,
    ("Embarcadero", "Marina District"): 12,
    
    # Financial District row:
    ("Financial District", "Presidio"): 22,
    ("Financial District", "Haight-Ashbury"): 19,
    ("Financial District", "Nob Hill"): 8,
    ("Financial District", "Russian Hill"): 11,
    ("Financial District", "North Beach"): 7,
    ("Financial District", "Chinatown"): 5,
    ("Financial District", "Union Square"): 9,
    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "Marina District"): 15,
    
    # Marina District row:
    ("Marina District", "Presidio"): 10,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "North Beach"): 11,
    ("Marina District", "Chinatown"): 15,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Embarcadero"): 14,
    ("Marina District", "Financial District"): 17,
}

# Create the Z3 solver instance.
s = Solver()

# Create integer variables for meeting start times (in minutes).
meeting_starts = [Int(f"start_{i}") for i in range(N)]

# Create integer variables for the position (order) in the schedule.
# order_vars[k] is the friend index scheduled at the k-th meeting.
order_vars = [Int(f"order_{k}") for k in range(N)]
s.add(Distinct(order_vars))
for k in range(N):
    s.add(And(order_vars[k] >= 0, order_vars[k] < N))

# For each meeting i, add the constraint that its start time is within its available window.
for i in range(N):
    avail = friends[i]
    s.add(meeting_starts[i] >= avail["avail_start"])
    s.add(meeting_starts[i] + avail["duration"] <= avail["avail_end"])

# Constraint: The first meeting must start after we travel from Presidio (arrival time = 9:00 = 540) 
# to the first meeting’s location.
for i in range(N):
    # If friend i is scheduled first then its start time must be at least 540 + travel time from Presidio.
    travel_time = travel[("Presidio", friends[i]["location"])]
    s.add(Implies(order_vars[0] == i, meeting_starts[i] >= 540 + travel_time))

# For every consecutive pair in the order, add travel constraints.
for pos in range(N-1):
    for i in range(N):
        for j in range(N):
            if i != j:
                # Travel time from friend i's location to friend j's location.
                ttime = travel.get((friends[i]["location"], friends[j]["location"]))
                # It may be that the pair is not defined; if so, skip (but here all needed pairs are provided).
                if ttime is not None:
                    s.add(Implies(And(order_vars[pos] == i, order_vars[pos+1] == j),
                                  meeting_starts[i] + friends[i]["duration"] + ttime <= meeting_starts[j]))

# (Optional) You could add an objective here to optimize some quantity (for instance, minimize the finish time of the last meeting)
# For this example we are simply finding a feasible schedule meeting all friends.

if s.check() == sat:
    model = s.model()
    # Retrieve the permutation (order). order_vars[0] ... order_vars[N-1]
    order_solution = [model.evaluate(order_vars[k]).as_long() for k in range(N)]
    
    # Create an ordered itinerary list.
    itinerary = []
    for pos in range(N):
        friend_index = order_solution[pos]
        start_val = model.evaluate(meeting_starts[friend_index]).as_long()
        end_val = start_val + friends[friend_index]["duration"]
        itinerary.append({
            "action": "meet",
            "person": friends[friend_index]["name"],
            "start_time": format_time(start_val),
            "end_time": format_time(end_val)
        })
        
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))
else:
    print("No solution found.")