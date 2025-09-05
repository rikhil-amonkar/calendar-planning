import json
from itertools import permutations

def parse_time(s):
    s = s.strip().upper()
    if s.endswith('AM'):
        hh, mm = map(int, s[:-2].split(':'))
        if hh == 12:
            hh = 0
    elif s.endswith('PM'):
        hh, mm = map(int, s[:-2].split(':'))
        if hh != 12:
            hh += 12
    else:
        # already in 24h "H:MM" format
        hh, mm = map(int, s.split(':'))
    return hh * 60 + mm

def fmt_time(m):
    hh = m // 60
    mm = m % 60
    return f"{hh}:{mm:02d}"

# Locations
locs = [
    "Marina District",
    "Embarcadero",
    "Bayview",
    "Union Square",
    "Chinatown",
    "Sunset District",
    "Golden Gate Park",
    "Financial District",
    "Haight-Ashbury",
    "Mission District",
]

# Travel times (directed, in minutes)
T = {loc: {} for loc in locs}
for a in locs:
    T[a][a] = 0

# Fill travel times
travel_entries = [
    ("Marina District","Embarcadero",14),
    ("Marina District","Bayview",27),
    ("Marina District","Union Square",16),
    ("Marina District","Chinatown",15),
    ("Marina District","Sunset District",19),
    ("Marina District","Golden Gate Park",18),
    ("Marina District","Financial District",17),
    ("Marina District","Haight-Ashbury",16),
    ("Marina District","Mission District",20),
    ("Embarcadero","Marina District",12),
    ("Embarcadero","Bayview",21),
    ("Embarcadero","Union Square",10),
    ("Embarcadero","Chinatown",7),
    ("Embarcadero","Sunset District",30),
    ("Embarcadero","Golden Gate Park",25),
    ("Embarcadero","Financial District",5),
    ("Embarcadero","Haight-Ashbury",21),
    ("Embarcadero","Mission District",20),
    ("Bayview","Marina District",27),
    ("Bayview","Embarcadero",19),
    ("Bayview","Union Square",18),
    ("Bayview","Chinatown",19),
    ("Bayview","Sunset District",23),
    ("Bayview","Golden Gate Park",22),
    ("Bayview","Financial District",19),
    ("Bayview","Haight-Ashbury",19),
    ("Bayview","Mission District",13),
    ("Union Square","Marina District",18),
    ("Union Square","Embarcadero",11),
    ("Union Square","Bayview",15),
    ("Union Square","Chinatown",7),
    ("Union Square","Sunset District",27),
    ("Union Square","Golden Gate Park",22),
    ("Union Square","Financial District",9),
    ("Union Square","Haight-Ashbury",18),
    ("Union Square","Mission District",14),
    ("Chinatown","Marina District",12),
    ("Chinatown","Embarcadero",5),
    ("Chinatown","Bayview",20),
    ("Chinatown","Union Square",7),
    ("Chinatown","Sunset District",29),
    ("Chinatown","Golden Gate Park",23),
    ("Chinatown","Financial District",5),
    ("Chinatown","Haight-Ashbury",19),
    ("Chinatown","Mission District",17),
    ("Sunset District","Marina District",21),
    ("Sunset District","Embarcadero",30),
    ("Sunset District","Bayview",22),
    ("Sunset District","Union Square",30),
    ("Sunset District","Chinatown",30),
    ("Sunset District","Golden Gate Park",11),
    ("Sunset District","Financial District",30),
    ("Sunset District","Haight-Ashbury",15),
    ("Sunset District","Mission District",25),
    ("Golden Gate Park","Marina District",16),
    ("Golden Gate Park","Embarcadero",25),
    ("Golden Gate Park","Bayview",23),
    ("Golden Gate Park","Union Square",22),
    ("Golden Gate Park","Chinatown",23),
    ("Golden Gate Park","Sunset District",10),
    ("Golden Gate Park","Financial District",26),
    ("Golden Gate Park","Haight-Ashbury",7),
    ("Golden Gate Park","Mission District",17),
    ("Financial District","Marina District",15),
    ("Financial District","Embarcadero",4),
    ("Financial District","Bayview",19),
    ("Financial District","Union Square",9),
    ("Financial District","Chinatown",5),
    ("Financial District","Sunset District",30),
    ("Financial District","Golden Gate Park",23),
    ("Financial District","Haight-Ashbury",19),
    ("Financial District","Mission District",17),
    ("Haight-Ashbury","Marina District",17),
    ("Haight-Ashbury","Embarcadero",20),
    ("Haight-Ashbury","Bayview",18),
    ("Haight-Ashbury","Union Square",19),
    ("Haight-Ashbury","Chinatown",19),
    ("Haight-Ashbury","Sunset District",15),
    ("Haight-Ashbury","Golden Gate Park",7),
    ("Haight-Ashbury","Financial District",21),
    ("Haight-Ashbury","Mission District",11),
    ("Mission District","Marina District",19),
    ("Mission District","Embarcadero",19),
    ("Mission District","Bayview",14),
    ("Mission District","Union Square",15),
    ("Mission District","Chinatown",16),
    ("Mission District","Sunset District",24),
    ("Mission District","Golden Gate Park",17),
    ("Mission District","Financial District",15),
    ("Mission District","Haight-Ashbury",12),
]
for a,b,t in travel_entries:
    T[a][b] = t

def travel(a, b):
    return T[a][b]

# Friends constraints
friends = [
    {
        "name": "Joshua",
        "location": "Embarcadero",
        "start": parse_time("9:45AM"),
        "end": parse_time("6:00PM"),
        "min_duration": 105,
    },
    {
        "name": "Jeffrey",
        "location": "Bayview",
        "start": parse_time("9:45AM"),
        "end": parse_time("8:15PM"),
        "min_duration": 75,
    },
    {
        "name": "Charles",
        "location": "Union Square",
        "start": parse_time("10:45AM"),
        "end": parse_time("8:15PM"),
        "min_duration": 120,
    },
    {
        "name": "Joseph",
        "location": "Chinatown",
        "start": parse_time("7:00AM"),
        "end": parse_time("3:30PM"),
        "min_duration": 60,
    },
    {
        "name": "Elizabeth",
        "location": "Sunset District",
        "start": parse_time("9:00AM"),
        "end": parse_time("9:45AM"),
        "min_duration": 45,
    },
    {
        "name": "Matthew",
        "location": "Golden Gate Park",
        "start": parse_time("11:00AM"),
        "end": parse_time("7:30PM"),
        "min_duration": 45,
    },
    {
        "name": "Carol",
        "location": "Financial District",
        "start": parse_time("10:45AM"),
        "end": parse_time("11:15AM"),
        "min_duration": 15,
    },
    {
        "name": "Paul",
        "location": "Haight-Ashbury",
        "start": parse_time("7:15PM"),
        "end": parse_time("8:30PM"),
        "min_duration": 15,
    },
    {
        "name": "Rebecca",
        "location": "Mission District",
        "start": parse_time("5:00PM"),
        "end": parse_time("9:45PM"),
        "min_duration": 45,
    },
]

start_location = "Marina District"
start_time = parse_time("9:00AM")

# DFS search to find optimal schedule
best = {
    "score": (-1, -1, float('inf'), float('inf'), float('inf')),  # will be replaced
    "schedule": [],
}

# Precompute a map from name to index
name_to_idx = {f["name"]: i for i, f in enumerate(friends)}

def schedule_score(schedule, total_travel, total_wait):
    count = len(schedule)
    total_meet = sum(item["end"] - item["start"] for item in schedule)
    finish_time = schedule[-1]["end"] if schedule else start_time
    # Objective: maximize count, then total_meet, then minimize travel, then minimize wait, then earliest finish
    return (count, total_meet, total_travel, total_wait, finish_time)

def dfs(cur_loc, cur_time, met_mask, schedule, total_travel, total_wait):
    global best
    # Update best solution
    sc = schedule_score(schedule, total_travel, total_wait)
    if (sc[0] > best["score"][0] or
        (sc[0] == best["score"][0] and sc[1] > best["score"][1]) or
        (sc[0] == best["score"][0] and sc[1] == best["score"][1] and sc[2] < best["score"][2]) or
        (sc[0] == best["score"][0] and sc[1] == best["score"][1] and sc[2] == best["score"][2] and sc[3] < best["score"][3]) or
        (sc[0] == best["score"][0] and sc[1] == best["score"][1] and sc[2] == best["score"][2] and sc[3] == best["score"][3] and sc[4] < best["score"][4])
       ):
        best["score"] = sc
        best["schedule"] = list(schedule)

    n = len(friends)

    # Simple upper-bound pruning: remaining potential meetings at most n - current_count
    remaining_possible = n - bin(met_mask).count("1")
    if sc[0] + remaining_possible < best["score"][0]:
        return

    # Try meeting each remaining friend next
    for i, f in enumerate(friends):
        if (met_mask >> i) & 1:
            continue
        travel_time = travel(cur_loc, f["location"])
        arrival = cur_time + travel_time
        latest_start = f["end"] - f["min_duration"]
        if arrival > latest_start:
            continue
        start_mt = max(arrival, f["start"])
        end_mt = start_mt + f["min_duration"]
        if end_mt > f["end"]:
            continue
        wait_here = max(0, start_mt - arrival)
        schedule.append({
            "action": "meet",
            "location": f["location"],
            "person": f["name"],
            "start": start_mt,
            "end": end_mt,
        })
        dfs(
            f["location"],
            end_mt,
            met_mask | (1 << i),
            schedule,
            total_travel + travel_time,
            total_wait + wait_here
        )
        schedule.pop()

# Run search
dfs(start_location, start_time, 0, [], 0, 0)

# Prepare output
output = {"itinerary": []}
for item in best["schedule"]:
    output["itinerary"].append({
        "action": item["action"],
        "location": item["location"],
        "person": item["person"],
        "start_time": fmt_time(item["start"]),
        "end_time": fmt_time(item["end"]),
    })

print(json.dumps(output, ensure_ascii=False))