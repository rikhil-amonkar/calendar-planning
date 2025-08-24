"SOLUTION:"
import itertools
import json

# Helper functions
def parse_time(tstr):
    h, m = tstr.split(":")
    return int(h) * 60 + int(m)

def minutes_to_str(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Build directed travel time map (in minutes)
places = [
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

dist = {p: {} for p in places}

def add(a, b, t):
    dist[a][b] = t

# Given travel distances (directed)
add("Presidio", "Haight-Ashbury", 15)
add("Presidio", "Nob Hill", 18)
add("Presidio", "Russian Hill", 14)
add("Presidio", "North Beach", 18)
add("Presidio", "Chinatown", 21)
add("Presidio", "Union Square", 22)
add("Presidio", "Embarcadero", 20)
add("Presidio", "Financial District", 23)
add("Presidio", "Marina District", 11)

add("Haight-Ashbury", "Presidio", 15)
add("Haight-Ashbury", "Nob Hill", 15)
add("Haight-Ashbury", "Russian Hill", 17)
add("Haight-Ashbury", "North Beach", 19)
add("Haight-Ashbury", "Chinatown", 19)
add("Haight-Ashbury", "Union Square", 19)
add("Haight-Ashbury", "Embarcadero", 20)
add("Haight-Ashbury", "Financial District", 21)
add("Haight-Ashbury", "Marina District", 17)

add("Nob Hill", "Presidio", 17)
add("Nob Hill", "Haight-Ashbury", 13)
add("Nob Hill", "Russian Hill", 5)
add("Nob Hill", "North Beach", 8)
add("Nob Hill", "Chinatown", 6)
add("Nob Hill", "Union Square", 7)
add("Nob Hill", "Embarcadero", 9)
add("Nob Hill", "Financial District", 9)
add("Nob Hill", "Marina District", 11)

add("Russian Hill", "Presidio", 14)
add("Russian Hill", "Haight-Ashbury", 17)
add("Russian Hill", "Nob Hill", 5)
add("Russian Hill", "North Beach", 5)
add("Russian Hill", "Chinatown", 9)
add("Russian Hill", "Union Square", 10)
add("Russian Hill", "Embarcadero", 8)
add("Russian Hill", "Financial District", 11)
add("Russian Hill", "Marina District", 7)

add("North Beach", "Presidio", 17)
add("North Beach", "Haight-Ashbury", 18)
add("North Beach", "Nob Hill", 7)
add("North Beach", "Russian Hill", 4)
add("North Beach", "Chinatown", 6)
add("North Beach", "Union Square", 7)
add("North Beach", "Embarcadero", 6)
add("North Beach", "Financial District", 8)
add("North Beach", "Marina District", 9)

add("Chinatown", "Presidio", 19)
add("Chinatown", "Haight-Ashbury", 19)
add("Chinatown", "Nob Hill", 9)
add("Chinatown", "Russian Hill", 7)
add("Chinatown", "North Beach", 3)
add("Chinatown", "Union Square", 7)
add("Chinatown", "Embarcadero", 5)
add("Chinatown", "Financial District", 5)
add("Chinatown", "Marina District", 12)

add("Union Square", "Presidio", 24)
add("Union Square", "Haight-Ashbury", 18)
add("Union Square", "Nob Hill", 9)
add("Union Square", "Russian Hill", 13)
add("Union Square", "North Beach", 10)
add("Union Square", "Chinatown", 7)
add("Union Square", "Embarcadero", 11)
add("Union Square", "Financial District", 9)
add("Union Square", "Marina District", 18)

add("Embarcadero", "Presidio", 20)
add("Embarcadero", "Haight-Ashbury", 21)
add("Embarcadero", "Nob Hill", 10)
add("Embarcadero", "Russian Hill", 8)
add("Embarcadero", "North Beach", 5)
add("Embarcadero", "Chinatown", 7)
add("Embarcadero", "Union Square", 10)
add("Embarcadero", "Financial District", 5)
add("Embarcadero", "Marina District", 12)

add("Financial District", "Presidio", 22)
add("Financial District", "Haight-Ashbury", 19)
add("Financial District", "Nob Hill", 8)
add("Financial District", "Russian Hill", 11)
add("Financial District", "North Beach", 7)
add("Financial District", "Chinatown", 5)
add("Financial District", "Union Square", 9)
add("Financial District", "Embarcadero", 4)
add("Financial District", "Marina District", 15)

add("Marina District", "Presidio", 10)
add("Marina District", "Haight-Ashbury", 16)
add("Marina District", "Nob Hill", 12)
add("Marina District", "Russian Hill", 8)
add("Marina District", "North Beach", 11)
add("Marina District", "Chinatown", 15)
add("Marina District", "Union Square", 16)
add("Marina District", "Embarcadero", 14)
add("Marina District", "Financial District", 17)

# People constraints
people = [
    {
        "name": "Karen",
        "location": "Haight-Ashbury",
        "start": parse_time("21:00"),
        "end": parse_time("21:45"),
        "min_duration": 45,
    },
    {
        "name": "Jessica",
        "location": "Nob Hill",
        "start": parse_time("13:45"),
        "end": parse_time("21:00"),
        "min_duration": 90,
    },
    {
        "name": "Brian",
        "location": "Russian Hill",
        "start": parse_time("15:30"),
        "end": parse_time("21:45"),
        "min_duration": 60,
    },
    {
        "name": "Kenneth",
        "location": "North Beach",
        "start": parse_time("9:45"),
        "end": parse_time("21:00"),
        "min_duration": 30,
    },
    {
        "name": "Jason",
        "location": "Chinatown",
        "start": parse_time("8:15"),
        "end": parse_time("11:45"),
        "min_duration": 75,
    },
    {
        "name": "Stephanie",
        "location": "Union Square",
        "start": parse_time("14:45"),
        "end": parse_time("18:45"),
        "min_duration": 105,
    },
    {
        "name": "Kimberly",
        "location": "Embarcadero",
        "start": parse_time("9:45"),
        "end": parse_time("19:30"),
        "min_duration": 75,
    },
    {
        "name": "Steven",
        "location": "Financial District",
        "start": parse_time("7:15"),
        "end": parse_time("21:15"),
        "min_duration": 60,
    },
    {
        "name": "Mark",
        "location": "Marina District",
        "start": parse_time("10:15"),
        "end": parse_time("13:00"),
        "min_duration": 75,
    },
]

people_by_name = {p["name"]: p for p in people}
names = [p["name"] for p in people]

start_location = "Presidio"
start_time = parse_time("9:00")

best_score = None
best_schedule = None

# Objective: maximize count of meetings; tie-breakers: minimize total travel, minimize waiting, minimize finish time
def evaluate_schedule(schedule, travel_total, wait_total, finish_time):
    count = len(schedule)
    # We maximize a tuple; for minimization components, negate them
    return (count, -travel_total, -wait_total, -finish_time)

# Try all permutations of meeting orders
for order in itertools.permutations(names):
    cur_loc = start_location
    cur_time = start_time
    travel_total = 0
    wait_total = 0
    sched = []
    for nm in order:
        p = people_by_name[nm]
        # travel time; if not defined, skip (shouldn't happen)
        t = dist[cur_loc].get(p["location"], None)
        if t is None:
            continue
        arrival = cur_time + t
        start_meet = max(arrival, p["start"])
        finish_meet = start_meet + p["min_duration"]
        if finish_meet <= p["end"]:
            # feasible meeting
            travel_total += t
            wait = max(0, p["start"] - arrival) if arrival < p["start"] else 0
            wait_total += wait
            sched.append({
                "action": "meet",
                "location": p["location"],
                "person": p["name"],
                "start_time": minutes_to_str(start_meet),
                "end_time": minutes_to_str(finish_meet),
                "_start_min": start_meet,
                "_end_min": finish_meet,
            })
            cur_loc = p["location"]
            cur_time = finish_meet
        else:
            # not feasible in this order; skip this person
            continue

    if sched:
        finish_time = sched[-1]["_end_min"]
    else:
        finish_time = start_time

    score = evaluate_schedule(sched, travel_total, wait_total, finish_time)
    if best_score is None or score > best_score:
        best_score = score
        best_schedule = sched

# Prepare final JSON output
# Remove helper fields and ensure formatting is correct
output_schedule = []
for item in best_schedule or []:
    output_schedule.append({
        "action": item["action"],
        "location": item["location"],
        "person": item["person"],
        "start_time": item["start_time"],
        "end_time": item["end_time"],
    })

result = {"itinerary": output_schedule}
print(json.dumps(result, ensure_ascii=False))