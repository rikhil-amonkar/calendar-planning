import itertools
import json

# Helper functions for time
def parse_time(s):
    h, m = s.split(":")
    return int(h) * 60 + int(m)

def fmt_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Build travel time dictionary (directed, minutes)
travel = {
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Bayview"): 23,
    ("Golden Gate Park", "Mission District"): 17,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "Financial District"): 26,

    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "Financial District"): 11,

    ("Bayview", "Golden Gate Park"): 22,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Bayview", "Mission District"): 13,
    ("Bayview", "Embarcadero"): 19,
    ("Bayview", "Financial District"): 19,

    ("Mission District", "Golden Gate Park"): 17,
    ("Mission District", "Fisherman's Wharf"): 22,
    ("Mission District", "Bayview"): 15,
    ("Mission District", "Embarcadero"): 19,
    ("Mission District", "Financial District"): 17,

    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Embarcadero", "Bayview"): 21,
    ("Embarcadero", "Mission District"): 20,
    ("Embarcadero", "Financial District"): 5,

    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Financial District", "Bayview"): 19,
    ("Financial District", "Mission District"): 17,
    ("Financial District", "Embarcadero"): 4,
}

def ttime(src, dst):
    return travel[(src, dst)]

# People constraints
people = [
    {
        "name": "Joseph",
        "loc": "Fisherman's Wharf",
        "start": parse_time("8:00"),
        "end": parse_time("17:30"),
        "min": 90
    },
    {
        "name": "Jeffrey",
        "loc": "Bayview",
        "start": parse_time("17:30"),
        "end": parse_time("21:30"),
        "min": 60
    },
    {
        "name": "Kevin",
        "loc": "Mission District",
        "start": parse_time("11:15"),
        "end": parse_time("15:15"),
        "min": 30
    },
    {
        "name": "David",
        "loc": "Embarcadero",
        "start": parse_time("8:15"),
        "end": parse_time("9:00"),
        "min": 30
    },
    {
        "name": "Barbara",
        "loc": "Financial District",
        "start": parse_time("10:30"),
        "end": parse_time("16:30"),
        "min": 15
    },
]

people_by_name = {p["name"]: p for p in people}

start_loc = "Golden Gate Park"
start_time = parse_time("9:00")

# Build a function to compute a base schedule for a given order of distinct people
def build_base_schedule(order):
    meetings = []  # list of dicts: person, loc, start, end, min_req
    cur_loc = start_loc
    cur_time = start_time
    for name in order:
        p = people_by_name[name]
        arrive = cur_time + ttime(cur_loc, p["loc"])
        st = max(arrive, p["start"])
        en = st + p["min"]
        if en > p["end"]:
            return None  # infeasible
        meetings.append({
            "person": name,
            "loc": p["loc"],
            "start": st,
            "end": en,
            "min": p["min"]
        })
        cur_loc = p["loc"]
        cur_time = en
    # Backward extension to fill slack before next meeting (not extending final)
    for i in range(len(meetings) - 2, -1, -1):
        curr = meetings[i]
        nxt = meetings[i + 1]
        p_curr = people_by_name[curr["person"]]
        max_end = min(p_curr["end"], nxt["start"] - ttime(curr["loc"], nxt["loc"]))
        if max_end > curr["end"]:
            curr["end"] = max_end
    return meetings

# Fill gaps between meetings with optional extra sessions
def fill_gaps(base_meetings):
    # We treat base meetings as fixed commitments with given start times.
    # We'll insert filler meetings in gaps to minimize idle time.
    all_people = list(people_by_name.values())

    result_meets = []
    cur_loc = start_loc
    cur_time = start_time

    # helper to compute best filler before target meeting 'm'
    def choose_best_filler(cur_loc, cur_time, m):
        best = None
        base_arrival = cur_time + ttime(cur_loc, m["loc"])
        base_idle = max(0, m["start"] - base_arrival)
        if base_idle <= 0:
            return None  # no gap
        for f in all_people:
            # It's allowed to pick any friend as filler, including ones already in base.
            d1 = ttime(cur_loc, f["loc"])
            arrival_f = cur_time + d1
            start_f = max(arrival_f, f["start"])
            # Must be able to leave f to reach m by its start
            d2 = ttime(f["loc"], m["loc"])
            end_f_max = min(f["end"], m["start"] - d2)
            if end_f_max <= start_f:
                continue  # cannot fit
            idle_wait = max(0, f["start"] - arrival_f)
            meet_time = end_f_max - start_f
            # leftover idle after meeting and travel to m
            leftover_idle = m["start"] - (start_f + meet_time + d2)
            total_idle = idle_wait + leftover_idle
            improvement = base_idle - total_idle
            if improvement > 0:
                cand = {
                    "friend": f,
                    "start": start_f,
                    "end": end_f_max,
                    "idle_wait": idle_wait,
                    "total_idle_after": total_idle,
                    "improvement": improvement
                }
                if (best is None or
                    cand["improvement"] > best["improvement"] or
                    (cand["improvement"] == best["improvement"] and (d1 + d2) < (ttime(best["friend"]["loc"], m["loc"]) + ttime(cur_loc, best["friend"]["loc"])))):
                    best = cand
        return best

    for idx, m in enumerate(base_meetings):
        # Fill gap before m
        while True:
            best = choose_best_filler(cur_loc, cur_time, m)
            if best is None:
                break
            # Append filler meeting
            result_meets.append({
                "person": best["friend"]["name"],
                "loc": best["friend"]["loc"],
                "start": best["start"],
                "end": best["end"]
            })
            # Update current state to end of filler
            cur_loc = best["friend"]["loc"]
            cur_time = best["end"]
        # Now proceed to base meeting m
        # Ensure arrival feasible
        arrival = cur_time + ttime(cur_loc, m["loc"])
        # If we somehow arrive after m.start (shouldn't), skip infeasible
        if arrival > m["start"]:
            return None  # infeasible due to filler choices (should not happen with our chooser)
        # Base meeting starts at m.start
        result_meets.append({
            "person": m["person"],
            "loc": m["loc"],
            "start": m["start"],
            "end": m["end"]
        })
        cur_time = m["end"]
        cur_loc = m["loc"]
    return result_meets

def compute_metrics(schedule):
    # schedule: list of meeting segments with start/end, loc, person
    # Compute travel, idle, makespan, and counts
    cur_loc = start_loc
    cur_time = start_time
    total_travel = 0
    total_idle = 0
    last_end = start_time
    # Aggregate durations per person
    dur_by_person = {}
    for seg in schedule:
        # travel
        d = ttime(cur_loc, seg["loc"])
        total_travel += d
        arrival = cur_time + d
        if seg["start"] > arrival:
            total_idle += seg["start"] - arrival
        # update
        cur_loc = seg["loc"]
        cur_time = seg["end"]
        last_end = seg["end"]
        dur_by_person.setdefault(seg["person"], 0)
        dur_by_person[seg["person"]] += max(0, seg["end"] - seg["start"])
    # Compute friends met: those with duration >= min requirement
    friends_met = 0
    for p in people:
        if dur_by_person.get(p["name"], 0) >= p["min"]:
            friends_met += 1
    makespan = last_end - start_time
    total_meeting_time = sum(seg["end"] - seg["start"] for seg in schedule)
    return {
        "friends_met": friends_met,
        "travel": total_travel,
        "idle": total_idle,
        "makespan": makespan,
        "meeting_time": total_meeting_time,
        "end_time": last_end
    }

# Generate candidate base orders: all permutations of all subsets
persons = [p["name"] for p in people]

best = None
best_schedule = None

# We will explore all ordered subsets (arrangements)
for k in range(len(persons) + 1):
    for order in itertools.permutations(persons, k):
        # Build base schedule
        base = build_base_schedule(order)
        if base is None:
            continue
        # Fill gaps greedily
        filled = fill_gaps(base)
        if filled is None:
            continue
        metrics = compute_metrics(filled)
        # Score: maximize friends_met, then minimize idle, then minimize travel, then minimize makespan
        score = (metrics["friends_met"], -metrics["idle"], -metrics["travel"], -metrics["makespan"])
        if (best is None) or (score > best["score"]):
            best = {
                "score": score,
                "metrics": metrics
            }
            best_schedule = filled

# Format output JSON
output = {"itinerary": []}
for seg in best_schedule:
    output["itinerary"].append({
        "action": "meet",
        "location": seg["loc"],
        "person": seg["person"],
        "start_time": fmt_time(seg["start"]),
        "end_time": fmt_time(seg["end"])
    })

print(json.dumps(output, ensure_ascii=False))