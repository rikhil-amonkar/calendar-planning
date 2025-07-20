import json

def format_time(minutes):
    total_hours = minutes // 60
    total_minutes = minutes % 60
    hour = 9 + total_hours
    return f"{hour}:{total_minutes:02d}"

travel_times = {
    "Marina District": {
        "Embarcadero": 14,
        "Bayview": 27,
        "Union Square": 16,
        "Chinatown": 15,
        "Sunset District": 19,
        "Golden Gate Park": 18,
        "Financial District": 17,
        "Haight-Ashbury": 16,
        "Mission District": 20
    },
    "Embarcadero": {
        "Marina District": 12,
        "Bayview": 21,
        "Union Square": 10,
        "Chinatown": 7,
        "Sunset District": 30,
        "Golden Gate Park": 25,
        "Financial District": 5,
        "Haight-Ashbury": 21,
        "Mission District": 20
    },
    "Bayview": {
        "Marina District": 27,
        "Embarcadero": 19,
        "Union Square": 18,
        "Chinatown": 19,
        "Sunset District": 23,
        "Golden Gate Park": 22,
        "Financial District": 19,
        "Haight-Ashbury": 19,
        "Mission District": 13
    },
    "Union Square": {
        "Marina District": 18,
        "Embarcadero": 11,
        "Bayview": 15,
        "Chinatown": 7,
        "Sunset District": 27,
        "Golden Gate Park": 22,
        "Financial District": 9,
        "Haight-Ashbury": 18,
        "Mission District": 14
    },
    "Chinatown": {
        "Marina District": 12,
        "Embarcadero": 5,
        "Bayview": 20,
        "Union Square": 7,
        "Sunset District": 29,
        "Golden Gate Park": 23,
        "Financial District": 5,
        "Haight-Ashbury": 19,
        "Mission District": 17
    },
    "Sunset District": {
        "Marina District": 21,
        "Embarcadero": 30,
        "Bayview": 22,
        "Union Square": 30,
        "Chinatown": 30,
        "Golden Gate Park": 11,
        "Financial District": 30,
        "Haight-Ashbury": 15,
        "Mission District": 25
    },
    "Golden Gate Park": {
        "Marina District": 16,
        "Embarcadero": 25,
        "Bayview": 23,
        "Union Square": 22,
        "Chinatown": 23,
        "Sunset District": 10,
        "Financial District": 26,
        "Haight-Ashbury": 7,
        "Mission District": 17
    },
    "Financial District": {
        "Marina District": 15,
        "Embarcadero": 4,
        "Bayview": 19,
        "Union Square": 9,
        "Chinatown": 5,
        "Sunset District": 30,
        "Golden Gate Park": 23,
        "Haight-Ashbury": 19,
        "Mission District": 17
    },
    "Haight-Ashbury": {
        "Marina District": 17,
        "Embarcadero": 20,
        "Bayview": 18,
        "Union Square": 19,
        "Chinatown": 19,
        "Sunset District": 15,
        "Golden Gate Park": 7,
        "Financial District": 21,
        "Mission District": 11
    },
    "Mission District": {
        "Marina District": 19,
        "Embarcadero": 19,
        "Bayview": 14,
        "Union Square": 15,
        "Chinatown": 16,
        "Sunset District": 24,
        "Golden Gate Park": 17,
        "Financial District": 15,
        "Haight-Ashbury": 12
    }
}

for loc in travel_times:
    travel_times[loc][loc] = 0

friends = [
    {"name": "Joshua", "location": "Embarcadero", "start": 45, "end": 540, "duration": 105},
    {"name": "Jeffrey", "location": "Bayview", "start": 45, "end": 675, "duration": 75},
    {"name": "Charles", "location": "Union Square", "start": 105, "end": 675, "duration": 120},
    {"name": "Joseph", "location": "Chinatown", "start": 0, "end": 390, "duration": 60},
    {"name": "Matthew", "location": "Golden Gate Park", "start": 120, "end": 630, "duration": 45},
    {"name": "Carol", "location": "Financial District", "start": 105, "end": 135, "duration": 15},
    {"name": "Paul", "location": "Haight-Ashbury", "start": 615, "end": 690, "duration": 15},
    {"name": "Rebecca", "location": "Mission District", "start": 480, "end": 765, "duration": 45}
]

dp = {}
parent = {}

dp[0] = {"Marina District": 0}

for state in range(0, 256):
    if state not in dp:
        continue
    for loc in list(dp[state].keys()):
        current_time = dp[state][loc]
        for i, friend in enumerate(friends):
            if state & (1 << i):
                continue
            next_loc = friend['location']
            tt = travel_times[loc][next_loc]
            arrival = current_time + tt
            start = max(arrival, friend['start'])
            end = start + friend['duration']
            if end <= friend['end']:
                new_state = state | (1 << i)
                if new_state not in dp:
                    dp[new_state] = {}
                if next_loc not in dp[new_state] or end < dp[new_state][next_loc]:
                    dp[new_state][next_loc] = end
                    if new_state not in parent:
                        parent[new_state] = {}
                    parent[new_state][next_loc] = (state, loc, i)

max_count = -1
best_state = None
best_loc = None
best_time = None
for state, loc_dict in dp.items():
    count = bin(state).count("1")
    if count > max_count:
        max_count = count
        best_state = state
        best_loc = None
        best_time = None
        for loc_name, time_val in loc_dict.items():
            if best_loc is None or time_val < best_time:
                best_loc = loc_name
                best_time = time_val
    elif count == max_count:
        for loc_name, time_val in loc_dict.items():
            if best_loc is None or time_val < best_time:
                best_loc = loc_name
                best_time = time_val

itinerary_events = []
if best_state != 0:
    state = best_state
    loc = best_loc
    while state != 0:
        if state not in parent or loc not in parent[state]:
            break
        prev_state, prev_loc, i = parent[state][loc]
        friend = friends[i]
        end_time_val = dp[state][loc]
        start_time_val = end_time_val - friend['duration']
        event = {
            "action": "meet",
            "location": friend['location'],
            "person": friend['name'],
            "start_time": format_time(start_time_val),
            "end_time": format_time(end_time_val)
        }
        itinerary_events.append(event)
        state = prev_state
        loc = prev_loc
    itinerary_events.reverse()

result = {
    "itinerary": itinerary_events
}

print(json.dumps(result, indent=2))