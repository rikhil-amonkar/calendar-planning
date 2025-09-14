import json
from z3 import *

def minutes(h, m):
    return h * 60 + m

def parse_time(tstr):
    # 'H:MM' format without leading zero for hour
    h, m = tstr.split(':')
    return int(h) * 60 + int(m)

def fmt_time(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

def main():
    # Travel times in minutes (directed)
    travel = {
        "Financial District": {
            "Golden Gate Park": 23,
            "Chinatown": 5,
            "Union Square": 9,
            "Fisherman's Wharf": 10,
            "Pacific Heights": 13,
            "North Beach": 7,
        },
        "Golden Gate Park": {
            "Financial District": 26,
            "Chinatown": 23,
            "Union Square": 22,
            "Fisherman's Wharf": 24,
            "Pacific Heights": 16,
            "North Beach": 24,
        },
        "Chinatown": {
            "Financial District": 5,
            "Golden Gate Park": 23,
            "Union Square": 7,
            "Fisherman's Wharf": 8,
            "Pacific Heights": 10,
            "North Beach": 3,
        },
        "Union Square": {
            "Financial District": 9,
            "Golden Gate Park": 22,
            "Chinatown": 7,
            "Fisherman's Wharf": 15,
            "Pacific Heights": 15,
            "North Beach": 10,
        },
        "Fisherman's Wharf": {
            "Financial District": 11,
            "Golden Gate Park": 25,
            "Chinatown": 12,
            "Union Square": 13,
            "Pacific Heights": 12,
            "North Beach": 6,
        },
        "Pacific Heights": {
            "Financial District": 13,
            "Golden Gate Park": 15,
            "Chinatown": 11,
            "Union Square": 12,
            "Fisherman's Wharf": 13,
            "North Beach": 9,
        },
        "North Beach": {
            "Financial District": 8,
            "Golden Gate Park": 22,
            "Chinatown": 6,
            "Union Square": 7,
            "Fisherman's Wharf": 5,
            "Pacific Heights": 8,
        },
    }

    # People constraints
    people = [
        {
            "name": "Stephanie",
            "location": "Golden Gate Park",
            "avail_start": "11:00",
            "avail_end": "15:00",
            "min_duration": 105,
        },
        {
            "name": "Karen",
            "location": "Chinatown",
            "avail_start": "13:45",
            "avail_end": "16:30",
            "min_duration": 15,
        },
        {
            "name": "Brian",
            "location": "Union Square",
            "avail_start": "15:00",
            "avail_end": "17:15",
            "min_duration": 30,
        },
        {
            "name": "Rebecca",
            "location": "Fisherman's Wharf",
            "avail_start": "8:00",
            "avail_end": "11:15",
            "min_duration": 30,
        },
        {
            "name": "Joseph",
            "location": "Pacific Heights",
            "avail_start": "8:15",
            "avail_end": "9:30",
            "min_duration": 60,
        },
        {
            "name": "Steven",
            "location": "North Beach",
            "avail_start": "14:30",
            "avail_end": "20:45",
            "min_duration": 120,
        },
    ]

    # Convert availability strings to minutes
    for p in people:
        p["avail_start_m"] = parse_time(p["avail_start"])
        p["avail_end_m"] = parse_time(p["avail_end"])

    start_loc = "Financial District"
    arrival_time = parse_time("9:00")  # Arrive at Financial District at 9:00

    opt = Optimize()

    # Decision variables
    starts = {}
    ends = {}
    meets = {}
    durations = {}

    for p in people:
        name = p["name"]
        starts[name] = Int(f"start_{name}")
        ends[name] = Int(f"end_{name}")
        meets[name] = Bool(f"meet_{name}")
        durations[name] = Int(f"dur_{name}")
        # General domain constraints
        opt.add(starts[name] >= 0)
        opt.add(ends[name] >= 0)
        opt.add(durations[name] >= 0)
        # Duration definition
        opt.add(Implies(meets[name], durations[name] == ends[name] - starts[name]))
        opt.add(Implies(Not(meets[name]), durations[name] == 0))

        # Availability and minimum duration (only if meeting)
        opt.add(Implies(meets[name], And(
            starts[name] >= p["avail_start_m"],
            ends[name] <= p["avail_end_m"],
            ends[name] - starts[name] >= p["min_duration"],
            ends[name] > starts[name]
        )))
        # If not meeting, set start=end=0 for cleanliness (optional)
        opt.add(Implies(Not(meets[name]), And(starts[name] == 0, ends[name] == 0)))

        # Reachability from the starting location at day start
        # Ensures that any meeting (including the first) is not earlier than can be reached from start.
        # This is safe/redundant for subsequent meetings but preserves feasibility.
        t_from_start = travel[start_loc][p["location"]]
        opt.add(Implies(meets[name], starts[name] >= arrival_time + t_from_start))

    # Pairwise non-overlap with travel times between meetings
    for i in range(len(people)):
        for j in range(i + 1, len(people)):
            pi = people[i]
            pj = people[j]
            ni = pi["name"]
            nj = pj["name"]
            li = pi["location"]
            lj = pj["location"]
            tij = travel[li][lj]
            tji = travel[lj][li]
            opt.add(Implies(And(meets[ni], meets[nj]),
                            Or(ends[ni] + tij <= starts[nj],
                               ends[nj] + tji <= starts[ni])))

    # Objective: maximize number of meetings
    meet_count = Sum([If(meets[p["name"]], 1, 0) for p in people])
    h1 = opt.maximize(meet_count)

    # Tiebreaker: minimize latest end time among meetings
    latest_end = Int("latest_end")
    opt.add(latest_end >= 0)
    for p in people:
        name = p["name"]
        opt.add(latest_end >= If(meets[name], ends[name], 0))
    h2 = opt.minimize(latest_end)

    # Additional tiebreaker: minimize total meeting time (prefer tight/minimum feasible)
    total_meeting_time = Sum([durations[p["name"]] for p in people])
    h3 = opt.minimize(total_meeting_time)

    if opt.check() != sat:
        # If unsat, output empty itinerary
        print(json.dumps({"itinerary": []}, ensure_ascii=False))
        return

    model = opt.model()

    itinerary = []
    for p in people:
        name = p["name"]
        if is_true(model.evaluate(meets[name])):
            s = model.evaluate(starts[name]).as_long()
            e = model.evaluate(ends[name]).as_long()
            itinerary.append({
                "action": "meet",
                "location": p["location"],
                "person": name,
                "start_time": fmt_time(s),
                "end_time": fmt_time(e)
            })

    # Sort by start time
    itinerary.sort(key=lambda x: parse_time(x["start_time"]))

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()