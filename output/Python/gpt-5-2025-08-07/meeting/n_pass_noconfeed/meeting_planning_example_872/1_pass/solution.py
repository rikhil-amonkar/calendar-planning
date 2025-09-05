import json
from itertools import permutations

def time_to_minutes(h, m):
    return h * 60 + m

def minutes_to_str(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

# Locations
L = [
    "Presidio",
    "Haight-Ashbury",
    "Nob Hill",
    "Russian Hill",
    "North Beach",
    "Chinatown",
    "Union Square",
    "Embarcadero",
    "Financial District",
    "Marina District",
]

# Travel times (directed, in minutes)
T = {loc: {} for loc in L}
def tt(a, b, v):
    T[a][b] = v

# Presidio
tt("Presidio", "Haight-Ashbury", 15)
tt("Presidio", "Nob Hill", 18)
tt("Presidio", "Russian Hill", 14)
tt("Presidio", "North Beach", 18)
tt("Presidio", "Chinatown", 21)
tt("Presidio", "Union Square", 22)
tt("Presidio", "Embarcadero", 20)
tt("Presidio", "Financial District", 23)
tt("Presidio", "Marina District", 11)

# Haight-Ashbury
tt("Haight-Ashbury", "Presidio", 15)
tt("Haight-Ashbury", "Nob Hill", 15)
tt("Haight-Ashbury", "Russian Hill", 17)
tt("Haight-Ashbury", "North Beach", 19)
tt("Haight-Ashbury", "Chinatown", 19)
tt("Haight-Ashbury", "Union Square", 19)
tt("Haight-Ashbury", "Embarcadero", 20)
tt("Haight-Ashbury", "Financial District", 21)
tt("Haight-Ashbury", "Marina District", 17)

# Nob Hill
tt("Nob Hill", "Presidio", 17)
tt("Nob Hill", "Haight-Ashbury", 13)
tt("Nob Hill", "Russian Hill", 5)
tt("Nob Hill", "North Beach", 8)
tt("Nob Hill", "Chinatown", 6)
tt("Nob Hill", "Union Square", 7)
tt("Nob Hill", "Embarcadero", 9)
tt("Nob Hill", "Financial District", 9)
tt("Nob Hill", "Marina District", 11)

# Russian Hill
tt("Russian Hill", "Presidio", 14)
tt("Russian Hill", "Haight-Ashbury", 17)
tt("Russian Hill", "Nob Hill", 5)
tt("Russian Hill", "North Beach", 5)
tt("Russian Hill", "Chinatown", 9)
tt("Russian Hill", "Union Square", 10)
tt("Russian Hill", "Embarcadero", 8)
tt("Russian Hill", "Financial District", 11)
tt("Russian Hill", "Marina District", 7)

# North Beach
tt("North Beach", "Presidio", 17)
tt("North Beach", "Haight-Ashbury", 18)
tt("North Beach", "Nob Hill", 7)
tt("North Beach", "Russian Hill", 4)
tt("North Beach", "Chinatown", 6)
tt("North Beach", "Union Square", 7)
tt("North Beach", "Embarcadero", 6)
tt("North Beach", "Financial District", 8)
tt("North Beach", "Marina District", 9)

# Chinatown
tt("Chinatown", "Presidio", 19)
tt("Chinatown", "Haight-Ashbury", 19)
tt("Chinatown", "Nob Hill", 9)
tt("Chinatown", "Russian Hill", 7)
tt("Chinatown", "North Beach", 3)
tt("Chinatown", "Union Square", 7)
tt("Chinatown", "Embarcadero", 5)
tt("Chinatown", "Financial District", 5)
tt("Chinatown", "Marina District", 12)

# Union Square
tt("Union Square", "Presidio", 24)
tt("Union Square", "Haight-Ashbury", 18)
tt("Union Square", "Nob Hill", 9)
tt("Union Square", "Russian Hill", 13)
tt("Union Square", "North Beach", 10)
tt("Union Square", "Chinatown", 7)
tt("Union Square", "Embarcadero", 11)
tt("Union Square", "Financial District", 9)
tt("Union Square", "Marina District", 18)

# Embarcadero
tt("Embarcadero", "Presidio", 20)
tt("Embarcadero", "Haight-Ashbury", 21)
tt("Embarcadero", "Nob Hill", 10)
tt("Embarcadero", "Russian Hill", 8)
tt("Embarcadero", "North Beach", 5)
tt("Embarcadero", "Chinatown", 7)
tt("Embarcadero", "Union Square", 10)
tt("Embarcadero", "Financial District", 5)
tt("Embarcadero", "Marina District", 12)

# Financial District
tt("Financial District", "Presidio", 22)
tt("Financial District", "Haight-Ashbury", 19)
tt("Financial District", "Nob Hill", 8)
tt("Financial District", "Russian Hill", 11)
tt("Financial District", "North Beach", 7)
tt("Financial District", "Chinatown", 5)
tt("Financial District", "Union Square", 9)
tt("Financial District", "Embarcadero", 4)
tt("Financial District", "Marina District", 15)

# Marina District
tt("Marina District", "Presidio", 10)
tt("Marina District", "Haight-Ashbury", 16)
tt("Marina District", "Nob Hill", 12)
tt("Marina District", "Russian Hill", 8)
tt("Marina District", "North Beach", 11)
tt("Marina District", "Chinatown", 15)
tt("Marina District", "Union Square", 16)
tt("Marina District", "Embarcadero", 14)
tt("Marina District", "Financial District", 17)

# Zero time to stay in place
for a in L:
    T[a][a] = 0

# Friends and constraints
friends = {
    "Karen": {
        "location": "Haight-Ashbury",
        "start": time_to_minutes(21, 0),
        "end": time_to_minutes(21, 45),
        "duration": 45,
    },
    "Jessica": {
        "location": "Nob Hill",
        "start": time_to_minutes(13, 45),
        "end": time_to_minutes(21, 0),
        "duration": 90,
    },
    "Brian": {
        "location": "Russian Hill",
        "start": time_to_minutes(15, 30),
        "end": time_to_minutes(21, 45),
        "duration": 60,
    },
    "Kenneth": {
        "location": "North Beach",
        "start": time_to_minutes(9, 45),
        "end": time_to_minutes(21, 0),
        "duration": 30,
    },
    "Jason": {
        "location": "Chinatown",
        "start": time_to_minutes(8, 15),
        "end": time_to_minutes(11, 45),
        "duration": 75,
    },
    "Stephanie": {
        "location": "Union Square",
        "start": time_to_minutes(14, 45),
        "end": time_to_minutes(18, 45),
        "duration": 105,
    },
    "Kimberly": {
        "location": "Embarcadero",
        "start": time_to_minutes(9, 45),
        "end": time_to_minutes(19, 30),
        "duration": 75,
    },
    "Steven": {
        "location": "Financial District",
        "start": time_to_minutes(7, 15),
        "end": time_to_minutes(21, 15),
        "duration": 60,
    },
    "Mark": {
        "location": "Marina District",
        "start": time_to_minutes(10, 15),
        "end": time_to_minutes(13, 0),
        "duration": 75,
    },
}

start_location = "Presidio"
start_time = time_to_minutes(9, 0)

names = list(friends.keys())

# Utility to attempt scheduling a meeting next
def schedule_next(current_loc, current_time, person_name):
    f = friends[person_name]
    travel = T[current_loc][f["location"]]
    arrival = current_time + travel
    start = max(arrival, f["start"])
    end = start + f["duration"]
    if end > f["end"]:
        return None  # infeasible
    return {
        "person": person_name,
        "location": f["location"],
        "start": start,
        "end": end,
        "travel": travel,
    }

best_plan = None

def evaluate_plan(plan):
    # Objective: maximize number met, then total meeting time, then earliest finish, then minimal travel
    count = len(plan)
    total_meeting = sum(item["end"] - item["start"] for item in plan)
    finish_time = plan[-1]["end"] if plan else start_time
    total_travel = 0
    if plan:
        # travel into first meeting from start
        total_travel += T[start_location][plan[0]["location"]]
        # then between meetings
        for i in range(1, len(plan)):
            total_travel += T[plan[i-1]["location"]][plan[i]["location"]]
    return (count, total_meeting, -finish_time, -total_travel)  # higher is better except finish/travel we negate

def search(current_loc, current_time, remaining, plan):
    global best_plan

    # Update best if current plan is better
    if best_plan is None or evaluate_plan(plan) > evaluate_plan(best_plan):
        best_plan = plan[:]

    # Upper bound pruning: even if we meet everyone remaining, cannot beat current best
    potential_max = len(plan) + len(remaining)
    if best_plan is not None and potential_max < len(best_plan):
        return

    # Try candidates ordered by earlier window end to reduce dead ends
    candidates = sorted(list(remaining), key=lambda n: friends[n]["end"])
    for name in candidates:
        res = schedule_next(current_loc, current_time, name)
        if res is None:
            continue
        # feasible; proceed
        remaining_next = set(remaining)
        remaining_next.remove(name)
        plan.append({
            "action": "meet",
            "location": res["location"],
            "person": name,
            "start": res["start"],
            "end": res["end"],
        })
        search(res["location"], res["end"], remaining_next, plan)
        plan.pop()

# Run the search
search(start_location, start_time, set(names), [])

# Prepare output
output = {"itinerary": []}
if best_plan:
    # Ensure chronological order (already is, but sort just in case)
    best_plan_sorted = sorted(best_plan, key=lambda x: x["start"])
    for item in best_plan_sorted:
        output["itinerary"].append({
            "action": "meet",
            "location": item["location"],
            "person": item["person"],
            "start_time": minutes_to_str(item["start"]),
            "end_time": minutes_to_str(item["end"]),
        })

print(json.dumps(output, ensure_ascii=False))