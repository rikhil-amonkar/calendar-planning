import json

def minutes_to_str(m):
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

# Travel times (in minutes)
travel = {
    "Richmond District": {
        "The Castro": 16,
        "Nob Hill": 17,
        "Marina District": 9,
        "Pacific Heights": 10,
        "Haight-Ashbury": 10,
        "Mission District": 20,
        "Chinatown": 20,
        "Russian Hill": 13,
        "Alamo Square": 13,
        "Bayview": 27
    },
    "The Castro": {
        "Richmond District": 16,
        "Nob Hill": 16,
        "Marina District": 21,
        "Pacific Heights": 16,
        "Haight-Ashbury": 6,
        "Mission District": 7,
        "Chinatown": 22,
        "Russian Hill": 18,
        "Alamo Square": 8,
        "Bayview": 19
    },
    "Nob Hill": {
        "Richmond District": 14,
        "The Castro": 17,
        "Marina District": 11,
        "Pacific Heights": 8,
        "Haight-Ashbury": 13,
        "Mission District": 13,
        "Chinatown": 6,
        "Russian Hill": 5,
        "Alamo Square": 11,
        "Bayview": 19
    },
    "Marina District": {
        "Richmond District": 11,
        "The Castro": 22,
        "Nob Hill": 12,
        "Pacific Heights": 7,
        "Haight-Ashbury": 16,
        "Mission District": 20,
        "Chinatown": 15,
        "Russian Hill": 8,
        "Alamo Square": 15,
        "Bayview": 27
    },
    "Pacific Heights": {
        "Richmond District": 12,
        "The Castro": 16,
        "Nob Hill": 8,
        "Marina District": 6,
        "Haight-Ashbury": 11,
        "Mission District": 15,
        "Chinatown": 11,
        "Russian Hill": 7,
        "Alamo Square": 10,
        "Bayview": 22
    },
    "Haight-Ashbury": {
        "Richmond District": 10,
        "The Castro": 6,
        "Nob Hill": 15,
        "Marina District": 17,
        "Pacific Heights": 12,
        "Mission District": 11,
        "Chinatown": 19,
        "Russian Hill": 17,
        "Alamo Square": 5,
        "Bayview": 18
    },
    "Mission District": {
        "Richmond District": 20,
        "The Castro": 7,
        "Nob Hill": 12,
        "Marina District": 19,
        "Pacific Heights": 16,
        "Haight-Ashbury": 12,
        "Chinatown": 16,
        "Russian Hill": 15,
        "Alamo Square": 11,
        "Bayview": 14
    },
    "Chinatown": {
        "Richmond District": 20,
        "The Castro": 22,
        "Nob Hill": 9,
        "Marina District": 12,
        "Pacific Heights": 10,
        "Haight-Ashbury": 19,
        "Mission District": 17,
        "Russian Hill": 7,
        "Alamo Square": 17,
        "Bayview": 20
    },
    "Russian Hill": {
        "Richmond District": 14,
        "The Castro": 21,
        "Nob Hill": 5,
        "Marina District": 7,
        "Pacific Heights": 7,
        "Haight-Ashbury": 17,
        "Mission District": 16,
        "Chinatown": 9,
        "Alamo Square": 15,
        "Bayview": 23
    },
    "Alamo Square": {
        "Richmond District": 11,
        "The Castro": 8,
        "Nob Hill": 11,
        "Marina District": 15,
        "Pacific Heights": 10,
        "Haight-Ashbury": 5,
        "Mission District": 10,
        "Chinatown": 15,
        "Russian Hill": 13,
        "Bayview": 16
    },
    "Bayview": {
        "Richmond District": 25,
        "The Castro": 19,
        "Nob Hill": 20,
        "Marina District": 27,
        "Pacific Heights": 23,
        "Haight-Ashbury": 19,
        "Mission District": 13,
        "Chinatown": 19,
        "Russian Hill": 23,
        "Alamo Square": 16
    }
}

def get_travel(a, b):
    if a == b:
        return 0
    return travel[a][b]

# Helper to create time in minutes
def t(h, m):
    return h * 60 + m

# Meeting constraints
start_location = "Richmond District"
arrival_time = t(9,0)

people = [
    {"name": "Matthew", "location": "The Castro", "start": t(16,30), "end": t(20,0), "min": 45},
    {"name": "Rebecca", "location": "Nob Hill", "start": t(15,15), "end": t(19,15), "min": 105},
    {"name": "Brian", "location": "Marina District", "start": t(14,15), "end": t(22,0), "min": 30},
    {"name": "Emily", "location": "Pacific Heights", "start": t(11,15), "end": t(19,45), "min": 15},
    {"name": "Karen", "location": "Haight-Ashbury", "start": t(11,45), "end": t(17,30), "min": 30},
    {"name": "Stephanie", "location": "Mission District", "start": t(13,0), "end": t(15,45), "min": 75},
    {"name": "James", "location": "Chinatown", "start": t(14,30), "end": t(19,0), "min": 120},
    {"name": "Steven", "location": "Russian Hill", "start": t(14,0), "end": t(20,0), "min": 30},
    {"name": "Elizabeth", "location": "Alamo Square", "start": t(13,0), "end": t(17,15), "min": 120},
    {"name": "William", "location": "Bayview", "start": t(18,15), "end": t(20,15), "min": 90},
]

# Precompute latest starts
for p in people:
    p["latest_start"] = p["end"] - p["min"]

n = len(people)

best = {
    "count": 0,
    "total_meeting": 0,
    "total_travel": 0,
    "finish_time": arrival_time,
    "itinerary": []
}

# Map person index for mask
indices = list(range(n))

def optimistic_bound(curr_time, visited_mask):
    # optimistic number of additional meetings: count those whose latest_start >= curr_time
    additional = 0
    for i in indices:
        if (visited_mask >> i) & 1:
            continue
        if people[i]["latest_start"] >= curr_time:
            additional += 1
    return additional

def dfs(curr_loc, curr_time, visited_mask, itinerary, total_meeting, total_travel):
    # Prune by optimistic bound
    current_count = len(itinerary)
    if current_count + optimistic_bound(curr_time, visited_mask) <= best["count"]:
        return

    # Update best
    improved = False
    if current_count > best["count"]:
        improved = True
    elif current_count == best["count"]:
        if total_meeting > best["total_meeting"]:
            improved = True
        elif total_meeting == best["total_meeting"]:
            if total_travel < best["total_travel"]:
                improved = True
            elif total_travel == best["total_travel"]:
                if curr_time < best["finish_time"]:
                    improved = True
    if improved:
        best["count"] = current_count
        best["total_meeting"] = total_meeting
        best["total_travel"] = total_travel
        best["finish_time"] = curr_time
        best["itinerary"] = list(itinerary)

    # Generate feasible next meetings
    candidates = []
    for i in indices:
        if (visited_mask >> i) & 1:
            continue
        p = people[i]
        tr = get_travel(curr_loc, p["location"])
        arrival = curr_time + tr
        # can wait until p["start"]
        start_time = max(arrival, p["start"])
        if start_time <= p["latest_start"]:
            end_time = start_time + p["min"]
            candidates.append((i, start_time, end_time, tr))

    # Order by urgency: earliest latest_start, then shortest meeting, then earliest feasible start
    candidates.sort(key=lambda x: (people[x[0]]["latest_start"], people[x[0]]["min"], x[1]))

    for i, start_time, end_time, tr in candidates:
        p = people[i]
        itinerary.append({
            "action": "meet",
            "location": p["location"],
            "person": p["name"],
            "start_time": minutes_to_str(start_time),
            "end_time": minutes_to_str(end_time)
        })
        dfs(
            p["location"],
            end_time,
            visited_mask | (1 << i),
            itinerary,
            total_meeting + p["min"],
            total_travel + tr
        )
        itinerary.pop()

# Start DFS
dfs(start_location, arrival_time, 0, [], 0, 0)

# Prepare output JSON
output = {
    "itinerary": best["itinerary"]
}

print(json.dumps(output, ensure_ascii=False))