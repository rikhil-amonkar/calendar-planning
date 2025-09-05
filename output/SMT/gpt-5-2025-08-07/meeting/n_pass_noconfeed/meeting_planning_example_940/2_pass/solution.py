import json
from z3 import Optimize, Int, Bool, If, Sum, And, Or, Implies, Not, sat, is_true

def minutes(h, m):
    return h * 60 + m

def fmt_time(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

def build_travel_times():
    # Locations
    L = [
        "Union Square",
        "Mission District",
        "Fisherman's Wharf",
        "Russian Hill",
        "Marina District",
        "North Beach",
        "Chinatown",
        "Pacific Heights",
        "The Castro",
        "Nob Hill",
        "Sunset District"
    ]
    tt = {a: {} for a in L}
    # Initialize self travel times
    for a in L:
        for b in L:
            if a == b:
                tt[a][b] = 0

    # Fill provided times
    tt["Union Square"]["Mission District"] = 14
    tt["Union Square"]["Fisherman's Wharf"] = 15
    tt["Union Square"]["Russian Hill"] = 13
    tt["Union Square"]["Marina District"] = 18
    tt["Union Square"]["North Beach"] = 10
    tt["Union Square"]["Chinatown"] = 7
    tt["Union Square"]["Pacific Heights"] = 15
    tt["Union Square"]["The Castro"] = 17
    tt["Union Square"]["Nob Hill"] = 9
    tt["Union Square"]["Sunset District"] = 27

    tt["Mission District"]["Union Square"] = 15
    tt["Mission District"]["Fisherman's Wharf"] = 22
    tt["Mission District"]["Russian Hill"] = 15
    tt["Mission District"]["Marina District"] = 19
    tt["Mission District"]["North Beach"] = 17
    tt["Mission District"]["Chinatown"] = 16
    tt["Mission District"]["Pacific Heights"] = 16
    tt["Mission District"]["The Castro"] = 7
    tt["Mission District"]["Nob Hill"] = 12
    tt["Mission District"]["Sunset District"] = 24

    tt["Fisherman's Wharf"]["Union Square"] = 13
    tt["Fisherman's Wharf"]["Mission District"] = 22
    tt["Fisherman's Wharf"]["Russian Hill"] = 7
    tt["Fisherman's Wharf"]["Marina District"] = 9
    tt["Fisherman's Wharf"]["North Beach"] = 6
    tt["Fisherman's Wharf"]["Chinatown"] = 12
    tt["Fisherman's Wharf"]["Pacific Heights"] = 12
    tt["Fisherman's Wharf"]["The Castro"] = 27
    tt["Fisherman's Wharf"]["Nob Hill"] = 11
    tt["Fisherman's Wharf"]["Sunset District"] = 27

    tt["Russian Hill"]["Union Square"] = 10
    tt["Russian Hill"]["Mission District"] = 16
    tt["Russian Hill"]["Fisherman's Wharf"] = 7
    tt["Russian Hill"]["Marina District"] = 7
    tt["Russian Hill"]["North Beach"] = 5
    tt["Russian Hill"]["Chinatown"] = 9
    tt["Russian Hill"]["Pacific Heights"] = 7
    tt["Russian Hill"]["The Castro"] = 21
    tt["Russian Hill"]["Nob Hill"] = 5
    tt["Russian Hill"]["Sunset District"] = 23

    tt["Marina District"]["Union Square"] = 16
    tt["Marina District"]["Mission District"] = 20
    tt["Marina District"]["Fisherman's Wharf"] = 10
    tt["Marina District"]["Russian Hill"] = 8
    tt["Marina District"]["North Beach"] = 11
    tt["Marina District"]["Chinatown"] = 15
    tt["Marina District"]["Pacific Heights"] = 7
    tt["Marina District"]["The Castro"] = 22
    tt["Marina District"]["Nob Hill"] = 12
    tt["Marina District"]["Sunset District"] = 19

    tt["North Beach"]["Union Square"] = 7
    tt["North Beach"]["Mission District"] = 18
    tt["North Beach"]["Fisherman's Wharf"] = 5
    tt["North Beach"]["Russian Hill"] = 4
    tt["North Beach"]["Marina District"] = 9
    tt["North Beach"]["Chinatown"] = 6
    tt["North Beach"]["Pacific Heights"] = 8
    tt["North Beach"]["The Castro"] = 23
    tt["North Beach"]["Nob Hill"] = 7
    tt["North Beach"]["Sunset District"] = 27

    tt["Chinatown"]["Union Square"] = 7
    tt["Chinatown"]["Mission District"] = 17
    tt["Chinatown"]["Fisherman's Wharf"] = 8
    tt["Chinatown"]["Russian Hill"] = 7
    tt["Chinatown"]["Marina District"] = 12
    tt["Chinatown"]["North Beach"] = 3
    tt["Chinatown"]["Pacific Heights"] = 10
    tt["Chinatown"]["The Castro"] = 22
    tt["Chinatown"]["Nob Hill"] = 9
    tt["Chinatown"]["Sunset District"] = 29

    tt["Pacific Heights"]["Union Square"] = 12
    tt["Pacific Heights"]["Mission District"] = 15
    tt["Pacific Heights"]["Fisherman's Wharf"] = 13
    tt["Pacific Heights"]["Russian Hill"] = 7
    tt["Pacific Heights"]["Marina District"] = 6
    tt["Pacific Heights"]["North Beach"] = 9
    tt["Pacific Heights"]["Chinatown"] = 11
    tt["Pacific Heights"]["The Castro"] = 16
    tt["Pacific Heights"]["Nob Hill"] = 8
    tt["Pacific Heights"]["Sunset District"] = 21

    tt["The Castro"]["Union Square"] = 19
    tt["The Castro"]["Mission District"] = 7
    tt["The Castro"]["Fisherman's Wharf"] = 24
    tt["The Castro"]["Russian Hill"] = 18
    tt["The Castro"]["Marina District"] = 21
    tt["The Castro"]["North Beach"] = 20
    tt["The Castro"]["Chinatown"] = 22
    tt["The Castro"]["Pacific Heights"] = 16
    tt["The Castro"]["Nob Hill"] = 16
    tt["The Castro"]["Sunset District"] = 17

    tt["Nob Hill"]["Union Square"] = 7
    tt["Nob Hill"]["Mission District"] = 13
    tt["Nob Hill"]["Fisherman's Wharf"] = 10
    tt["Nob Hill"]["Russian Hill"] = 5
    tt["Nob Hill"]["Marina District"] = 11
    tt["Nob Hill"]["North Beach"] = 8
    tt["Nob Hill"]["Chinatown"] = 6
    tt["Nob Hill"]["Pacific Heights"] = 8
    tt["Nob Hill"]["The Castro"] = 17
    tt["Nob Hill"]["Sunset District"] = 24

    tt["Sunset District"]["Union Square"] = 30
    tt["Sunset District"]["Mission District"] = 25
    tt["Sunset District"]["Fisherman's Wharf"] = 29
    tt["Sunset District"]["Russian Hill"] = 24
    tt["Sunset District"]["Marina District"] = 21
    tt["Sunset District"]["North Beach"] = 28
    tt["Sunset District"]["Chinatown"] = 30
    tt["Sunset District"]["Pacific Heights"] = 21
    tt["Sunset District"]["The Castro"] = 17
    tt["Sunset District"]["Nob Hill"] = 27

    return tt

def main():
    travel = build_travel_times()

    # Friends constraints
    friends = [
        {"name": "Kevin",   "location": "Mission District",      "start": minutes(20,45), "end": minutes(21,45), "min_dur": 60},
        {"name": "Mark",    "location": "Fisherman's Wharf",     "start": minutes(17,15), "end": minutes(20,0),  "min_dur": 90},
        {"name": "Jessica", "location": "Russian Hill",          "start": minutes(9,0),   "end": minutes(15,0),  "min_dur": 120},
        {"name": "Jason",   "location": "Marina District",       "start": minutes(15,15), "end": minutes(21,45), "min_dur": 120},
        {"name": "John",    "location": "North Beach",           "start": minutes(9,45),  "end": minutes(18,0),  "min_dur": 15},
        {"name": "Karen",   "location": "Chinatown",             "start": minutes(16,45), "end": minutes(19,0),  "min_dur": 75},
        {"name": "Sarah",   "location": "Pacific Heights",       "start": minutes(17,30), "end": minutes(18,15), "min_dur": 45},
        {"name": "Amanda",  "location": "The Castro",            "start": minutes(20,0),  "end": minutes(21,15), "min_dur": 60},
        {"name": "Nancy",   "location": "Nob Hill",              "start": minutes(9,45),  "end": minutes(13,0),  "min_dur": 45},
        {"name": "Rebecca", "location": "Sunset District",       "start": minutes(8,45),  "end": minutes(15,0),  "min_dur": 75},
    ]

    start_location = "Union Square"
    arrival_time = minutes(9,0)

    opt = Optimize()
    opt.set(priority='lex')

    # Variables for each friend
    s_vars = {}
    e_vars = {}
    meet_vars = {}

    # Time bounds
    min_time = 0
    max_time = minutes(23,59)

    for f in friends:
        name = f["name"]
        s = Int(f"s_{name}")
        e = Int(f"e_{name}")
        meet = Bool(f"meet_{name}")
        s_vars[name] = s
        e_vars[name] = e
        meet_vars[name] = meet

        # Bounds
        opt.add(s >= min_time, s <= max_time)
        opt.add(e >= min_time, e <= max_time)

        # If meeting, respect availability and duration, and first-reachability from start
        opt.add(Implies(meet,
                        And(s >= f["start"],
                            e <= f["end"],
                            e - s >= f["min_dur"],
                            s >= arrival_time + travel[start_location][f["location"]]
                        )))

        # If not meeting, set zero duration
        opt.add(Implies(Not(meet), e == s))

    # Pairwise disjunctive scheduling with travel times
    for i in range(len(friends)):
        for j in range(i+1, len(friends)):
            fi = friends[i]
            fj = friends[j]
            ni, nj = fi["name"], fj["name"]
            li, lj = fi["location"], fj["location"]
            si, ei, mi = s_vars[ni], e_vars[ni], meet_vars[ni]
            sj, ej, mj = s_vars[nj], e_vars[nj], meet_vars[nj]

            tij = travel[li][lj]
            tji = travel[lj][li]

            # If both meetings happen, either i before j with travel, or j before i with travel
            opt.add(Implies(And(mi, mj),
                            Or(ei + tij <= sj,
                               ej + tji <= si)))

    # Objectives: maximize number of meetings, then maximize total meeting minutes
    total_meetings = Sum([If(meet_vars[f["name"]], 1, 0) for f in friends])
    total_minutes = Sum([If(meet_vars[f["name"]], e_vars[f["name"]] - s_vars[f["name"]], 0) for f in friends])
    opt.maximize(total_meetings)
    opt.maximize(total_minutes)

    if opt.check() != sat:
        print(json.dumps({"itinerary": []}, indent=2))
        return

    model = opt.model()

    itinerary = []
    for f in friends:
        name = f["name"]
        meet_val = is_true(model.evaluate(meet_vars[name], model_completion=True))
        if meet_val:
            s_val = model.evaluate(s_vars[name]).as_long()
            e_val = model.evaluate(e_vars[name]).as_long()
            itinerary.append({
                "action": "meet",
                "location": f["location"],
                "person": name,
                "start_time": fmt_time(s_val),
                "end_time": fmt_time(e_val)
            })

    # Sort by start time
    itinerary.sort(key=lambda x: (int(x["start_time"].split(":")[0]) * 60 + int(x["start_time"].split(":")[1])))

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    main()