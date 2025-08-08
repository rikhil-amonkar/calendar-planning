import json
from itertools import combinations
from functools import lru_cache

# Helper functions
def parse_time_12h(tstr):
    # Expects formats like '8:45PM' or '10:00AM'
    tstr = tstr.strip().upper()
    if tstr.endswith('AM'):
        ampm = 'AM'
        core = tstr[:-2]
    elif tstr.endswith('PM'):
        ampm = 'PM'
        core = tstr[:-2]
    else:
        raise ValueError(f"Invalid time: {tstr}")
    core = core.strip()
    if ':' in core:
        h_str, m_str = core.split(':')
    else:
        h_str, m_str = core, '0'
    h = int(h_str)
    m = int(m_str)
    if ampm == 'AM':
        if h == 12:
            h = 0
    else:
        if h != 12:
            h += 12
    return h * 60 + m

def format_time_24h(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Build directed travel time map (in minutes)
locations = [
    "Sunset District",
    "Russian Hill",
    "The Castro",
    "Richmond District",
    "Marina District",
    "North Beach",
    "Union Square",
    "Golden Gate Park",
]

travel_list = [
    ("Sunset District","Russian Hill",24),
    ("Sunset District","The Castro",17),
    ("Sunset District","Richmond District",12),
    ("Sunset District","Marina District",21),
    ("Sunset District","North Beach",29),
    ("Sunset District","Union Square",30),
    ("Sunset District","Golden Gate Park",11),

    ("Russian Hill","Sunset District",23),
    ("Russian Hill","The Castro",21),
    ("Russian Hill","Richmond District",14),
    ("Russian Hill","Marina District",7),
    ("Russian Hill","North Beach",5),
    ("Russian Hill","Union Square",11),
    ("Russian Hill","Golden Gate Park",21),

    ("The Castro","Sunset District",17),
    ("The Castro","Russian Hill",18),
    ("The Castro","Richmond District",16),
    ("The Castro","Marina District",21),
    ("The Castro","North Beach",20),
    ("The Castro","Union Square",19),
    ("The Castro","Golden Gate Park",11),

    ("Richmond District","Sunset District",11),
    ("Richmond District","Russian Hill",13),
    ("Richmond District","The Castro",16),
    ("Richmond District","Marina District",9),
    ("Richmond District","North Beach",17),
    ("Richmond District","Union Square",21),
    ("Richmond District","Golden Gate Park",9),

    ("Marina District","Sunset District",19),
    ("Marina District","Russian Hill",8),
    ("Marina District","The Castro",22),
    ("Marina District","Richmond District",11),
    ("Marina District","North Beach",11),
    ("Marina District","Union Square",16),
    ("Marina District","Golden Gate Park",18),

    ("North Beach","Sunset District",27),
    ("North Beach","Russian Hill",4),
    ("North Beach","The Castro",22),
    ("North Beach","Richmond District",18),
    ("North Beach","Marina District",9),
    ("North Beach","Union Square",7),
    ("North Beach","Golden Gate Park",22),

    ("Union Square","Sunset District",26),
    ("Union Square","Russian Hill",13),
    ("Union Square","The Castro",19),
    ("Union Square","Richmond District",20),
    ("Union Square","Marina District",18),
    ("Union Square","North Beach",10),
    ("Union Square","Golden Gate Park",22),

    ("Golden Gate Park","Sunset District",10),
    ("Golden Gate Park","Russian Hill",19),
    ("Golden Gate Park","The Castro",13),
    ("Golden Gate Park","Richmond District",7),
    ("Golden Gate Park","Marina District",16),
    ("Golden Gate Park","North Beach",24),
    ("Golden Gate Park","Union Square",22),
]

travel = {frm: {} for frm in locations}
for frm, to, mins in travel_list:
    travel[frm][to] = mins
for loc in locations:
    travel[loc][loc] = 0  # zero to stay in place

def get_travel(a, b):
    return travel.get(a, {}).get(b, None)

# Meeting constraints
people = {
    "Karen": {
        "location": "Russian Hill",
        "start": parse_time_12h("8:45PM"),
        "end": parse_time_12h("9:45PM"),
        "min_dur": 60,
    },
    "Jessica": {
        "location": "The Castro",
        "start": parse_time_12h("3:45PM"),
        "end": parse_time_12h("7:30PM"),
        "min_dur": 60,
    },
    "Matthew": {
        "location": "Richmond District",
        "start": parse_time_12h("7:30AM"),
        "end": parse_time_12h("3:15PM"),
        "min_dur": 15,
    },
    "Michelle": {
        "location": "Marina District",
        "start": parse_time_12h("10:30AM"),
        "end": parse_time_12h("6:45PM"),
        "min_dur": 75,
    },
    "Carol": {
        "location": "North Beach",
        "start": parse_time_12h("12:00PM"),
        "end": parse_time_12h("5:00PM"),
        "min_dur": 90,
    },
    "Stephanie": {
        "location": "Union Square",
        "start": parse_time_12h("10:45AM"),
        "end": parse_time_12h("2:15PM"),
        "min_dur": 30,
    },
    "Linda": {
        "location": "Golden Gate Park",
        "start": parse_time_12h("10:45AM"),
        "end": parse_time_12h("10:00PM"),
        "min_dur": 90,
    },
}

start_location = "Sunset District"
start_time = parse_time_12h("9:00AM")

names = list(people.keys())

# Depth-first search to maximize number of meetings
best_solution = {
    "count": 0,
    "end_time": None,
    "total_wait": None,
    "total_travel": None,
    "itinerary": None,
}

def better(sol_a, sol_b):
    # Returns True if sol_a is better than sol_b
    if sol_b is None:
        return True
    if sol_a["count"] != sol_b["count"]:
        return sol_a["count"] > sol_b["count"]
    # tie-breaker: earliest end time
    if sol_a["end_time"] != sol_b["end_time"]:
        return sol_a["end_time"] < sol_b["end_time"]
    # next: minimal total waiting
    if sol_a["total_wait"] != sol_b["total_wait"]:
        return sol_a["total_wait"] < sol_b["total_wait"]
    # next: minimal travel time
    if sol_a["total_travel"] != sol_b["total_travel"]:
        return sol_a["total_travel"] < sol_b["total_travel"]
    # else arbitrary tie
    return False

def dfs(current_loc, current_time, remaining, itinerary, count, total_travel, total_wait):
    global best_solution
    # Update best with current itinerary (even if we can continue, current prefix is a valid solution)
    current_solution = {
        "count": count,
        "end_time": current_time,
        "total_wait": total_wait,
        "total_travel": total_travel,
        "itinerary": itinerary[:],
    }
    if better(current_solution, best_solution):
        best_solution = current_solution

    # Prune if even meeting everyone remaining can't beat best
    if count + len(remaining) < best_solution["count"]:
        return

    # Try each remaining person next
    for name in list(remaining):
        info = people[name]
        to_loc = info["location"]
        t_travel = get_travel(current_loc, to_loc)
        if t_travel is None:
            continue  # no path given (shouldn't happen)
        arrival = current_time + t_travel
        # Can wait until availability
        meeting_start = max(arrival, info["start"])
        meeting_end = meeting_start + info["min_dur"]
        if meeting_end > info["end"]:
            continue  # infeasible
        wait_time = max(0, info["start"] - arrival)
        # Recurse
        remaining_next = set(remaining)
        remaining_next.remove(name)
        itinerary_next = itinerary + [{
            "action": "meet",
            "location": to_loc,
            "person": name,
            "start": meeting_start,
            "end": meeting_end,
        }]
        dfs(
            to_loc,
            meeting_end,
            remaining_next,
            itinerary_next,
            count + 1,
            total_travel + t_travel,
            total_wait + wait_time
        )

# Start DFS
dfs(start_location, start_time, set(names), [], 0, 0, 0)

# Prepare output JSON
output_itinerary = []
for item in best_solution["itinerary"]:
    output_itinerary.append({
        "action": "meet",
        "location": item["location"],
        "person": item["person"],
        "start_time": format_time_24h(item["start"]),
        "end_time": format_time_24h(item["end"]),
    })

result = {"itinerary": output_itinerary}
print(json.dumps(result, ensure_ascii=False))