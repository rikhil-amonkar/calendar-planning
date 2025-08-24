import json

def minutes(h, m):
    return h * 60 + m

def min_to_str(m):
    h = m // 60
    mn = m % 60
    return f"{h}:{mn:02d}"

# Travel times (minutes)
travel = {
    "Nob Hill": {
        "Embarcadero": 9, "The Castro": 17, "Haight-Ashbury": 13, "Union Square": 7,
        "North Beach": 8, "Pacific Heights": 8, "Chinatown": 6, "Golden Gate Park": 17,
        "Marina District": 11, "Russian Hill": 5
    },
    "Embarcadero": {
        "Nob Hill": 10, "The Castro": 25, "Haight-Ashbury": 21, "Union Square": 10,
        "North Beach": 5, "Pacific Heights": 11, "Chinatown": 7, "Golden Gate Park": 25,
        "Marina District": 12, "Russian Hill": 8
    },
    "The Castro": {
        "Nob Hill": 16, "Embarcadero": 22, "Haight-Ashbury": 6, "Union Square": 19,
        "North Beach": 20, "Pacific Heights": 16, "Chinatown": 22, "Golden Gate Park": 11,
        "Marina District": 21, "Russian Hill": 18
    },
    "Haight-Ashbury": {
        "Nob Hill": 15, "Embarcadero": 20, "The Castro": 6, "Union Square": 19,
        "North Beach": 19, "Pacific Heights": 12, "Chinatown": 19, "Golden Gate Park": 7,
        "Marina District": 17, "Russian Hill": 17
    },
    "Union Square": {
        "Nob Hill": 9, "Embarcadero": 11, "The Castro": 17, "Haight-Ashbury": 18,
        "North Beach": 10, "Pacific Heights": 15, "Chinatown": 7, "Golden Gate Park": 22,
        "Marina District": 18, "Russian Hill": 13
    },
    "North Beach": {
        "Nob Hill": 7, "Embarcadero": 6, "The Castro": 23, "Haight-Ashbury": 18,
        "Union Square": 7, "Pacific Heights": 8, "Chinatown": 6, "Golden Gate Park": 22,
        "Marina District": 9, "Russian Hill": 4
    },
    "Pacific Heights": {
        "Nob Hill": 8, "Embarcadero": 10, "The Castro": 16, "Haight-Ashbury": 11,
        "Union Square": 12, "North Beach": 9, "Chinatown": 11, "Golden Gate Park": 15,
        "Marina District": 6, "Russian Hill": 7
    },
    "Chinatown": {
        "Nob Hill": 9, "Embarcadero": 5, "The Castro": 22, "Haight-Ashbury": 19,
        "Union Square": 7, "North Beach": 3, "Pacific Heights": 10, "Golden Gate Park": 23,
        "Marina District": 12, "Russian Hill": 7
    },
    "Golden Gate Park": {
        "Nob Hill": 20, "Embarcadero": 25, "The Castro": 13, "Haight-Ashbury": 7,
        "Union Square": 22, "North Beach": 23, "Pacific Heights": 16, "Chinatown": 23,
        "Marina District": 16, "Russian Hill": 19
    },
    "Marina District": {
        "Nob Hill": 12, "Embarcadero": 14, "The Castro": 22, "Haight-Ashbury": 16,
        "Union Square": 16, "North Beach": 11, "Pacific Heights": 7, "Chinatown": 15,
        "Golden Gate Park": 18, "Russian Hill": 8
    },
    "Russian Hill": {
        "Nob Hill": 5, "Embarcadero": 8, "The Castro": 21, "Haight-Ashbury": 17,
        "Union Square": 10, "North Beach": 5, "Pacific Heights": 7, "Chinatown": 9,
        "Golden Gate Park": 21, "Marina District": 7
    }
}
# Ensure self-travel is zero
for a in travel:
    travel[a][a] = 0

# Participants and constraints
people = [
    {
        "name": "Mary",
        "location": "Embarcadero",
        "start": minutes(20,0),
        "end": minutes(21,15),
        "min_dur": 75
    },
    {
        "name": "Kenneth",
        "location": "The Castro",
        "start": minutes(11,15),
        "end": minutes(19,15),
        "min_dur": 30
    },
    {
        "name": "Joseph",
        "location": "Haight-Ashbury",
        "start": minutes(20,0),
        "end": minutes(22,0),
        "min_dur": 120
    },
    {
        "name": "Sarah",
        "location": "Union Square",
        "start": minutes(11,45),
        "end": minutes(14,30),
        "min_dur": 90
    },
    {
        "name": "Thomas",
        "location": "North Beach",
        "start": minutes(19,15),
        "end": minutes(19,45),
        "min_dur": 15
    },
    {
        "name": "Daniel",
        "location": "Pacific Heights",
        "start": minutes(13,45),
        "end": minutes(20,30),
        "min_dur": 15
    },
    {
        "name": "Richard",
        "location": "Chinatown",
        "start": minutes(8,0),
        "end": minutes(18,45),
        "min_dur": 30
    },
    {
        "name": "Mark",
        "location": "Golden Gate Park",
        "start": minutes(17,30),
        "end": minutes(21,30),
        "min_dur": 120
    },
    {
        "name": "David",
        "location": "Marina District",
        "start": minutes(20,0),
        "end": minutes(21,0),
        "min_dur": 60
    },
    {
        "name": "Karen",
        "location": "Russian Hill",
        "start": minutes(13,15),
        "end": minutes(18,30),
        "min_dur": 120
    }
]

# Start state
start_location = "Nob Hill"
start_time = minutes(9, 0)

# Build index for people for bitmasking
for idx, p in enumerate(people):
    p["idx"] = idx

N = len(people)

best_solution = {
    "count": 0,
    "waiting": float('inf'),
    "end_time": start_time,
    "schedule": []
}

# Precompute an optimistic count function ignoring travel
def optimistic_remaining_count(current_time, visited_mask):
    cnt = 0
    for p in people:
        if not (visited_mask & (1 << p["idx"])):
            earliest = max(current_time, p["start"])
            if earliest + p["min_dur"] <= p["end"]:
                cnt += 1
    return cnt

# DFS with pruning
def dfs(current_loc, current_time, visited_mask, schedule, meetings_done, total_waiting):
    global best_solution

    # Prune by optimistic bound
    optimistic = optimistic_remaining_count(current_time, visited_mask)
    if meetings_done + optimistic < best_solution["count"]:
        return

    # Update best at leaf or intermediate
    if meetings_done > best_solution["count"] or (
        meetings_done == best_solution["count"] and (total_waiting < best_solution["waiting"] or
                                                     (total_waiting == best_solution["waiting"] and current_time < best_solution["end_time"]))
    ):
        best_solution = {
            "count": meetings_done,
            "waiting": total_waiting,
            "end_time": current_time,
            "schedule": list(schedule)
        }

    # Generate feasible next meetings
    candidates = []
    for p in people:
        if visited_mask & (1 << p["idx"]):
            continue
        travel_time = travel[current_loc][p["location"]]
        arrival = current_time + travel_time
        start_mt = max(arrival, p["start"])
        end_mt = start_mt + p["min_dur"]
        if end_mt <= p["end"]:
            # Candidate is feasible
            candidates.append((p, arrival, start_mt, end_mt))

    # Heuristic: explore by earliest meeting end time, then earliest window end
    candidates.sort(key=lambda x: (x[3], x[0]["end"]))

    for p, arrival, start_mt, end_mt in candidates:
        wait = max(0, start_mt - arrival)
        schedule.append({
            "action": "meet",
            "location": p["location"],
            "person": p["name"],
            "start_time": start_mt,
            "end_time": end_mt
        })
        dfs(
            p["location"],
            end_mt,
            visited_mask | (1 << p["idx"]),
            schedule,
            meetings_done + 1,
            total_waiting + wait
        )
        schedule.pop()

# Run search
dfs(start_location, start_time, 0, [], 0, 0)

# Build output JSON
output = {"itinerary": []}
for meeting in best_solution["schedule"]:
    output["itinerary"].append({
        "action": "meet",
        "location": meeting["location"],
        "person": meeting["person"],
        "start_time": min_to_str(meeting["start_time"]),
        "end_time": min_to_str(meeting["end_time"])
    })

print(json.dumps(output, ensure_ascii=False))