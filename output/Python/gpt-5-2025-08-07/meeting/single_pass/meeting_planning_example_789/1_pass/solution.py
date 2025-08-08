import json

def parse_ampm(s):
    s = s.strip().upper()
    if s.endswith('AM') or s.endswith('PM'):
        ampm = s[-2:]
        time_part = s[:-2]
    else:
        ampm = None
        time_part = s
    h, m = map(int, time_part.split(':'))
    if ampm == 'AM':
        if h == 12:
            h = 0
    elif ampm == 'PM':
        if h != 12:
            h += 12
    return h * 60 + m

def minutes_to_str(mins):
    h = mins // 60
    m = mins % 60
    return f"{h}:{m:02d}"

# Locations
locations = [
    "Union Square",
    "Russian Hill",
    "Alamo Square",
    "Haight-Ashbury",
    "Marina District",
    "Bayview",
    "Chinatown",
    "Presidio",
    "Sunset District",
]

# Directed travel times in minutes
tt = {
    "Union Square": {
        "Russian Hill": 13, "Alamo Square": 15, "Haight-Ashbury": 18, "Marina District": 18,
        "Bayview": 15, "Chinatown": 7, "Presidio": 24, "Sunset District": 27
    },
    "Russian Hill": {
        "Union Square": 10, "Alamo Square": 15, "Haight-Ashbury": 17, "Marina District": 7,
        "Bayview": 23, "Chinatown": 9, "Presidio": 14, "Sunset District": 23
    },
    "Alamo Square": {
        "Union Square": 14, "Russian Hill": 13, "Haight-Ashbury": 5, "Marina District": 15,
        "Bayview": 16, "Chinatown": 15, "Presidio": 17, "Sunset District": 16
    },
    "Haight-Ashbury": {
        "Union Square": 19, "Russian Hill": 17, "Alamo Square": 5, "Marina District": 17,
        "Bayview": 18, "Chinatown": 19, "Presidio": 15, "Sunset District": 15
    },
    "Marina District": {
        "Union Square": 16, "Russian Hill": 8, "Alamo Square": 15, "Haight-Ashbury": 16,
        "Bayview": 27, "Chinatown": 15, "Presidio": 10, "Sunset District": 19
    },
    "Bayview": {
        "Union Square": 18, "Russian Hill": 23, "Alamo Square": 16, "Haight-Ashbury": 19,
        "Marina District": 27, "Chinatown": 19, "Presidio": 32, "Sunset District": 23
    },
    "Chinatown": {
        "Union Square": 7, "Russian Hill": 7, "Alamo Square": 17, "Haight-Ashbury": 19,
        "Marina District": 12, "Bayview": 20, "Presidio": 19, "Sunset District": 29
    },
    "Presidio": {
        "Union Square": 22, "Russian Hill": 14, "Alamo Square": 19, "Haight-Ashbury": 15,
        "Marina District": 11, "Bayview": 31, "Chinatown": 21, "Sunset District": 15
    },
    "Sunset District": {
        "Union Square": 30, "Russian Hill": 24, "Alamo Square": 17, "Haight-Ashbury": 15,
        "Marina District": 21, "Bayview": 22, "Chinatown": 30, "Presidio": 16
    }
}

# Ensure all pairs exist and add zero diagonals
for a in locations:
    if a not in tt:
        tt[a] = {}
    for b in locations:
        if a == b:
            tt[a][b] = 0
        else:
            # If a->b missing, set to a large travel time (effectively blocks path)
            if b not in tt[a]:
                tt[a][b] = 10**9  # Very large to avoid selection

# Friends constraints
friends = [
    {"name": "Betty", "location": "Russian Hill", "start": parse_ampm("7:00AM"), "end": parse_ampm("4:45PM"), "min": 105},
    {"name": "Melissa", "location": "Alamo Square", "start": parse_ampm("9:30AM"), "end": parse_ampm("5:15PM"), "min": 105},
    {"name": "Joshua", "location": "Haight-Ashbury", "start": parse_ampm("12:15PM"), "end": parse_ampm("7:00PM"), "min": 90},
    {"name": "Jeffrey", "location": "Marina District", "start": parse_ampm("12:15PM"), "end": parse_ampm("6:00PM"), "min": 45},
    {"name": "James", "location": "Bayview", "start": parse_ampm("7:30AM"), "end": parse_ampm("8:00PM"), "min": 90},
    {"name": "Anthony", "location": "Chinatown", "start": parse_ampm("11:45AM"), "end": parse_ampm("1:30PM"), "min": 75},
    {"name": "Timothy", "location": "Presidio", "start": parse_ampm("12:30PM"), "end": parse_ampm("2:45PM"), "min": 90},
    {"name": "Emily", "location": "Sunset District", "start": parse_ampm("7:30PM"), "end": parse_ampm("9:30PM"), "min": 120},
]

start_location = "Union Square"
start_time = parse_ampm("9:00AM")

# Pre-sort friends by (end - min) to try tighter windows earlier in search
friends_sorted = sorted(friends, key=lambda f: (f["end"] - f["min"], f["end"]))

best = {
    "count": -1,
    "meeting_minutes": -1,
    "finish_time": 10**9,
    "travel": 10**9,
    "itinerary": []
}

def potential_count_upper_bound(current_time, remaining):
    # Upper bound on how many more could possibly be scheduled even with zero travel time
    cnt = 0
    for f in remaining:
        if current_time <= f["end"] - f["min"]:
            cnt += 1
    return cnt

def dfs(current_loc, current_time, remaining, itin, total_meeting, total_travel):
    # Update best with current itinerary
    curr_count = len(itin)
    finish_time = current_time
    improved = False
    if curr_count > best["count"]:
        improved = True
    elif curr_count == best["count"]:
        if total_meeting > best["meeting_minutes"]:
            improved = True
        elif total_meeting == best["meeting_minutes"]:
            if finish_time < best["finish_time"]:
                improved = True
            elif finish_time == best["finish_time"]:
                if total_travel < best["travel"]:
                    improved = True
    if improved:
        best["count"] = curr_count
        best["meeting_minutes"] = total_meeting
        best["finish_time"] = finish_time
        best["travel"] = total_travel
        best["itinerary"] = list(itin)

    # Prune if even optimistically we cannot beat current best count
    if curr_count + potential_count_upper_bound(current_time, remaining) < best["count"]:
        return

    # Try each remaining friend as next meeting
    for idx, f in enumerate(remaining):
        travel = tt[current_loc][f["location"]]
        if travel >= 10**9:
            continue
        arrival = current_time + travel
        start_meet = max(arrival, f["start"])
        end_meet = start_meet + f["min"]
        if end_meet <= f["end"]:
            next_remaining = remaining[:idx] + remaining[idx+1:]
            next_itin = itin + [{
                "action": "meet",
                "location": f["location"],
                "person": f["name"],
                "start": start_meet,
                "end": end_meet
            }]
            dfs(f["location"], end_meet, next_remaining, next_itin, total_meeting + f["min"], total_travel + travel)

# Run search
dfs(start_location, start_time, friends_sorted, [], 0, 0)

# Build output JSON
output_itinerary = []
for item in best["itinerary"]:
    output_itinerary.append({
        "action": "meet",
        "location": item["location"],
        "person": item["person"],
        "start_time": minutes_to_str(item["start"]),
        "end_time": minutes_to_str(item["end"])
    })

result = {"itinerary": output_itinerary}
print(json.dumps(result, ensure_ascii=False))