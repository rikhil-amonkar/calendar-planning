import json
from typing import List, Dict, Tuple

def parse_ampm(t: str) -> int:
    t = t.strip().upper()
    if t.endswith("AM"):
        ampm = "AM"
        t = t[:-2]
    elif t.endswith("PM"):
        ampm = "PM"
        t = t[:-2]
    else:
        raise ValueError("Time must end with AM or PM")
    h, m = map(int, t.split(":"))
    if ampm == "AM":
        if h == 12:
            h = 0
    else:
        if h != 12:
            h += 12
    return h * 60 + m

def fmt_time(minutes: int) -> str:
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Parse directed travel times from the given text
distances_text = """
Financial District to Fisherman's Wharf: 10.
Financial District to Presidio: 22.
Financial District to Bayview: 19.
Financial District to Haight-Ashbury: 19.
Financial District to Russian Hill: 11.
Financial District to The Castro: 20.
Financial District to Marina District: 15.
Financial District to Richmond District: 21.
Financial District to Union Square: 9.
Financial District to Sunset District: 30.
Fisherman's Wharf to Financial District: 11.
Fisherman's Wharf to Presidio: 17.
Fisherman's Wharf to Bayview: 26.
Fisherman's Wharf to Haight-Ashbury: 22.
Fisherman's Wharf to Russian Hill: 7.
Fisherman's Wharf to The Castro: 27.
Fisherman's Wharf to Marina District: 9.
Fisherman's Wharf to Richmond District: 18.
Fisherman's Wharf to Union Square: 13.
Fisherman's Wharf to Sunset District: 27.
Presidio to Financial District: 23.
Presidio to Fisherman's Wharf: 19.
Presidio to Bayview: 31.
Presidio to Haight-Ashbury: 15.
Presidio to Russian Hill: 14.
Presidio to The Castro: 21.
Presidio to Marina District: 11.
Presidio to Richmond District: 7.
Presidio to Union Square: 22.
Presidio to Sunset District: 15.
Bayview to Financial District: 19.
Bayview to Fisherman's Wharf: 25.
Bayview to Presidio: 32.
Bayview to Haight-Ashbury: 19.
Bayview to Russian Hill: 23.
Bayview to The Castro: 19.
Bayview to Marina District: 27.
Bayview to Richmond District: 25.
Bayview to Union Square: 18.
Bayview to Sunset District: 23.
Haight-Ashbury to Financial District: 21.
Haight-Ashbury to Fisherman's Wharf: 23.
Haight-Ashbury to Presidio: 15.
Haight-Ashbury to Bayview: 18.
Haight-Ashbury to Russian Hill: 17.
Haight-Ashbury to The Castro: 6.
Haight-Ashbury to Marina District: 17.
Haight-Ashbury to Richmond District: 10.
Haight-Ashbury to Union Square: 19.
Haight-Ashbury to Sunset District: 15.
Russian Hill to Financial District: 11.
Russian Hill to Fisherman's Wharf: 7.
Russian Hill to Presidio: 14.
Russian Hill to Bayview: 23.
Russian Hill to Haight-Ashbury: 17.
Russian Hill to The Castro: 21.
Russian Hill to Marina District: 7.
Russian Hill to Richmond District: 14.
Russian Hill to Union Square: 10.
Russian Hill to Sunset District: 23.
The Castro to Financial District: 21.
The Castro to Fisherman's Wharf: 24.
The Castro to Presidio: 20.
The Castro to Bayview: 19.
The Castro to Haight-Ashbury: 6.
The Castro to Russian Hill: 18.
The Castro to Marina District: 21.
The Castro to Richmond District: 16.
The Castro to Union Square: 19.
The Castro to Sunset District: 17.
Marina District to Financial District: 17.
Marina District to Fisherman's Wharf: 10.
Marina District to Presidio: 10.
Marina District to Bayview: 27.
Marina District to Haight-Ashbury: 16.
Marina District to Russian Hill: 8.
Marina District to The Castro: 22.
Marina District to Richmond District: 11.
Marina District to Union Square: 16.
Marina District to Sunset District: 19.
Richmond District to Financial District: 22.
Richmond District to Fisherman's Wharf: 18.
Richmond District to Presidio: 7.
Richmond District to Bayview: 27.
Richmond District to Haight-Ashbury: 10.
Richmond District to Russian Hill: 13.
Richmond District to The Castro: 16.
Richmond District to Marina District: 9.
Richmond District to Union Square: 21.
Richmond District to Sunset District: 11.
Union Square to Financial District: 9.
Union Square to Fisherman's Wharf: 15.
Union Square to Presidio: 24.
Union Square to Bayview: 15.
Union Square to Haight-Ashbury: 18.
Union Square to Russian Hill: 13.
Union Square to The Castro: 17.
Union Square to Marina District: 18.
Union Square to Richmond District: 20.
Union Square to Sunset District: 27.
Sunset District to Financial District: 30.
Sunset District to Fisherman's Wharf: 29.
Sunset District to Presidio: 16.
Sunset District to Bayview: 22.
Sunset District to Haight-Ashbury: 15.
Sunset District to Russian Hill: 24.
Sunset District to The Castro: 17.
Sunset District to Marina District: 21.
Sunset District to Richmond District: 12.
Sunset District to Union Square: 30.
"""

def build_travel_map(text: str) -> Dict[str, Dict[str, int]]:
    travel = {}
    lines = [ln.strip() for ln in text.strip().splitlines() if ln.strip()]
    for ln in lines:
        # Example: "Financial District to Fisherman's Wharf: 10."
        if ": " not in ln or " to " not in ln:
            continue
        left, right = ln.split(": ")
        minutes_str = right.strip().rstrip(".")
        minutes = int(minutes_str)
        origin, dest = left.split(" to ")
        if origin not in travel:
            travel[origin] = {}
        travel[origin][dest] = minutes
        # Ensure nodes exist
        if dest not in travel:
            travel[dest] = travel.get(dest, {})
    # set zero for same-location
    for a in list(travel.keys()):
        travel[a][a] = 0
    return travel

TRAVEL = build_travel_map(distances_text)

def travel_time(a: str, b: str) -> int:
    if a == b:
        return 0
    return TRAVEL[a][b]

# People constraints
people = [
    {
        "name": "Mark",
        "location": "Fisherman's Wharf",
        "start": parse_ampm("8:15AM"),
        "end": parse_ampm("10:00AM"),
        "min_duration": 30
    },
    {
        "name": "Stephanie",
        "location": "Presidio",
        "start": parse_ampm("12:15PM"),
        "end": parse_ampm("3:00PM"),
        "min_duration": 75
    },
    {
        "name": "Betty",
        "location": "Bayview",
        "start": parse_ampm("7:15AM"),
        "end": parse_ampm("8:30PM"),
        "min_duration": 15
    },
    {
        "name": "Lisa",
        "location": "Haight-Ashbury",
        "start": parse_ampm("3:30PM"),
        "end": parse_ampm("6:30PM"),
        "min_duration": 45
    },
    {
        "name": "William",
        "location": "Russian Hill",
        "start": parse_ampm("6:45PM"),
        "end": parse_ampm("8:00PM"),
        "min_duration": 60
    },
    {
        "name": "Brian",
        "location": "The Castro",
        "start": parse_ampm("9:15AM"),
        "end": parse_ampm("1:15PM"),
        "min_duration": 30
    },
    {
        "name": "Joseph",
        "location": "Marina District",
        "start": parse_ampm("10:45AM"),
        "end": parse_ampm("3:00PM"),
        "min_duration": 90
    },
    {
        "name": "Ashley",
        "location": "Richmond District",
        "start": parse_ampm("9:45AM"),
        "end": parse_ampm("11:15AM"),
        "min_duration": 45
    },
    {
        "name": "Patricia",
        "location": "Union Square",
        "start": parse_ampm("4:30PM"),
        "end": parse_ampm("8:00PM"),
        "min_duration": 120
    },
    {
        "name": "Karen",
        "location": "Sunset District",
        "start": parse_ampm("4:30PM"),
        "end": parse_ampm("10:00PM"),
        "min_duration": 105
    },
]

start_location = "Financial District"
start_time = parse_ampm("9:00AM")

# Map name -> person for quick lookup
people_by_name = {p["name"]: p for p in people}
names = [p["name"] for p in people]

# Precompute for ordering heuristic: window end
end_by_name = {p["name"]: p["end"] for p in people}

best = {
    "count": 0,
    "itinerary": [],
    "end_time": start_time,
    "total_travel": 0
}

def better(sol_a, sol_b):
    if sol_a["count"] != sol_b["count"]:
        return sol_a["count"] > sol_b["count"]
    if sol_a["end_time"] != sol_b["end_time"]:
        return sol_a["end_time"] < sol_b["end_time"]
    if sol_a["total_travel"] != sol_b["total_travel"]:
        return sol_a["total_travel"] < sol_b["total_travel"]
    return False

def dfs(current_loc: str, current_time: int, met: Tuple[str, ...], itinerary: List[Dict], total_travel: int):
    global best
    met_set = set(met)

    # Update best at leaf or intermediate
    curr_solution = {
        "count": len(itinerary),
        "itinerary": itinerary,
        "end_time": current_time,
        "total_travel": total_travel
    }
    if better(curr_solution, best):
        best = {
            "count": curr_solution["count"],
            "itinerary": list(curr_solution["itinerary"]),
            "end_time": curr_solution["end_time"],
            "total_travel": curr_solution["total_travel"]
        }

    # Upper bound prune: even if we met everyone remaining, cannot beat best
    remaining = [n for n in names if n not in met_set]
    if len(itinerary) + len(remaining) <= best["count"]:
        return

    # Build feasible candidates from current state
    candidates = []
    for name in remaining:
        p = people_by_name[name]
        t_travel = travel_time(current_loc, p["location"])
        arrival = current_time + t_travel
        start_meet = max(arrival, p["start"])
        end_meet = start_meet + p["min_duration"]
        if end_meet <= p["end"]:
            candidates.append((name, p, t_travel, start_meet, end_meet))

    if not candidates:
        return

    # Heuristic: try candidates in order of earlier availability end, then earlier feasible start
    candidates.sort(key=lambda x: (x[1]["end"], x[3], x[2]))

    for name, p, t_travel, start_meet, end_meet in candidates:
        new_itin = itinerary + [{
            "action": "meet",
            "location": p["location"],
            "person": name,
            "start_time": fmt_time(start_meet),
            "end_time": fmt_time(end_meet)
        }]
        dfs(
            p["location"],
            end_meet,
            tuple(sorted(list(met_set | {name}))),
            new_itin,
            total_travel + t_travel
        )

# Kick off search
dfs(start_location, start_time, tuple(), [], 0)

# Output JSON
output = {
    "itinerary": best["itinerary"]
}
print(json.dumps(output, ensure_ascii=False))