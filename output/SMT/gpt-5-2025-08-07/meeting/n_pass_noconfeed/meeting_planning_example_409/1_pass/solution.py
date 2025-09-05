import json
from z3 import *

def minutes(h, m):
    return h * 60 + m

def minutes_to_str(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

def build_shortest_paths(locations, edges):
    # Initialize adjacency matrix
    idx = {loc: i for i, loc in enumerate(locations)}
    n = len(locations)
    INF = 10**6
    dist = [[INF] * n for _ in range(n)]
    for i in range(n):
        dist[i][i] = 0
    for (u, v, t) in edges:
        i, j = idx[u], idx[v]
        dist[i][j] = min(dist[i][j], t)
    # Floyd-Warshall
    for k in range(n):
        for i in range(n):
            for j in range(n):
                if dist[i][k] + dist[k][j] < dist[i][j]:
                    dist[i][j] = dist[i][k] + dist[k][j]
    return dist, idx

def main():
    # Locations
    locations = [
        "Fisherman's Wharf",
        "Bayview",
        "Golden Gate Park",
        "Nob Hill",
        "Marina District",
        "Embarcadero"
    ]

    # Directed travel times (minutes)
    edges = [
        ("Fisherman's Wharf", "Bayview", 26),
        ("Fisherman's Wharf", "Golden Gate Park", 25),
        ("Fisherman's Wharf", "Nob Hill", 11),
        ("Fisherman's Wharf", "Marina District", 9),
        ("Fisherman's Wharf", "Embarcadero", 8),
        ("Bayview", "Fisherman's Wharf", 25),
        ("Bayview", "Golden Gate Park", 22),
        ("Bayview", "Nob Hill", 20),
        ("Bayview", "Marina District", 25),
        ("Bayview", "Embarcadero", 19),
        ("Golden Gate Park", "Fisherman's Wharf", 24),
        ("Golden Gate Park", "Bayview", 23),
        ("Golden Gate Park", "Nob Hill", 20),
        ("Golden Gate Park", "Marina District", 16),
        ("Golden Gate Park", "Embarcadero", 25),
        ("Nob Hill", "Fisherman's Wharf", 11),
        ("Nob Hill", "Bayview", 19),
        ("Nob Hill", "Golden Gate Park", 17),
        ("Nob Hill", "Marina District", 11),
        ("Nob Hill", "Embarcadero", 9),
        ("Marina District", "Fisherman's Wharf", 10),
        ("Marina District", "Bayview", 27),
        ("Marina District", "Golden Gate Park", 18),
        ("Marina District", "Nob Hill", 12),
        ("Marina District", "Embarcadero", 14),
        ("Embarcadero", "Fisherman's Wharf", 6),
        ("Embarcadero", "Bayview", 21),
        ("Embarcadero", "Golden Gate Park", 25),
        ("Embarcadero", "Nob Hill", 10),
        ("Embarcadero", "Marina District", 12),
    ]

    # Compute all-pairs shortest travel times
    sp, loc_idx = build_shortest_paths(locations, edges)

    # Day parameters
    start_location = "Fisherman's Wharf"
    arrival_time = minutes(9, 0)  # 9:00
    day_end = minutes(22, 0)      # 22:00

    # People constraints
    people = [
        {
            "name": "Thomas",
            "location": "Bayview",
            "avail_start": minutes(15, 30),
            "avail_end": minutes(18, 30),
            "min_duration": 120
        },
        {
            "name": "Stephanie",
            "location": "Golden Gate Park",
            "avail_start": minutes(18, 30),
            "avail_end": minutes(21, 45),
            "min_duration": 30
        },
        {
            "name": "Laura",
            "location": "Nob Hill",
            "avail_start": minutes(8, 45),
            "avail_end": minutes(16, 15),
            "min_duration": 30
        },
        {
            "name": "Betty",
            "location": "Marina District",
            "avail_start": minutes(18, 45),
            "avail_end": minutes(21, 45),
            "min_duration": 45
        },
        {
            "name": "Patricia",
            "location": "Embarcadero",
            "avail_start": minutes(17, 30),
            "avail_end": minutes(22, 0),
            "min_duration": 45
        },
    ]

    # Z3 variables
    opt = Optimize()
    opt.set(priority='lex')

    s_vars = {}
    e_vars = {}
    meet_vars = {}

    for p in people:
        base = p["name"].replace(" ", "_")
        s = Int(f"s_{base}")
        e = Int(f"e_{base}")
        meet = Bool(f"meet_{base}")
        s_vars[p["name"]] = s
        e_vars[p["name"]] = e
        meet_vars[p["name"]] = meet

        # Basic bounds
        opt.add(s >= 0, e >= 0, s <= e, e <= day_end)

        # If meeting, respect availability, duration, and reachability from start
        loc = p["location"]
        travel_from_start = sp[loc_idx[start_location]][loc_idx[loc]]
        opt.add(Implies(meet, And(
            s >= max(arrival_time, p["avail_start"]),
            e <= p["avail_end"],
            e - s >= p["min_duration"],
            s >= arrival_time + travel_from_start
        )))
        # If not meeting, set zero-length to simplify
        opt.add(Implies(Not(meet), e == s))

    # Non-overlap and travel feasibility between meetings
    n = len(people)
    for i in range(n):
        for j in range(i+1, n):
            pi = people[i]
            pj = people[j]
            li = loc_idx[pi["location"]]
            lj = loc_idx[pj["location"]]
            dij = sp[li][lj]
            dji = sp[lj][li]
            si, ei, mi = s_vars[pi["name"]], e_vars[pi["name"]], meet_vars[pi["name"]]
            sj, ej, mj = s_vars[pj["name"]], e_vars[pj["name"]], meet_vars[pj["name"]]
            opt.add(Implies(And(mi, mj), Or(ei + dij <= sj, ej + dji <= si)))

    # Objective 1: maximize number of friends met
    meet_count = Sum([If(meet_vars[p["name"]], 1, 0) for p in people])
    opt.maximize(meet_count)

    # Objective 2: maximize total meeting time
    total_meet_time = Sum([If(meet_vars[p["name"]], e_vars[p["name"]] - s_vars[p["name"]], 0) for p in people])
    opt.maximize(total_meet_time)

    # Solve
    if opt.check() != sat:
        print(json.dumps({"itinerary": []}))
        return

    model = opt.model()

    # Extract selected meetings
    meetings = []
    for p in people:
        if is_true(model.eval(meet_vars[p["name"]])):
            start_m = model.eval(s_vars[p["name"]]).as_long()
            end_m = model.eval(e_vars[p["name"]]).as_long()
            meetings.append({
                "person": p["name"],
                "location": p["location"],
                "start": start_m,
                "end": end_m
            })

    # Sort by start time
    meetings.sort(key=lambda x: x["start"])

    # Build JSON itinerary
    itinerary = []
    for m in meetings:
        itinerary.append({
            "action": "meet",
            "location": m["location"],
            "person": m["person"],
            "start_time": minutes_to_str(m["start"]),
            "end_time": minutes_to_str(m["end"])
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()