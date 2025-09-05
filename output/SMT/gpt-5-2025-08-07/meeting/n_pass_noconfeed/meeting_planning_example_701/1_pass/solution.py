import json
from z3 import Optimize, Int, Bool, And, Or, Implies, Not, If, Sum

def minutes(h, m):
    return h * 60 + m

def to_hhmm(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

def main():
    # Locations
    L = [
        "Mission District",
        "The Castro",
        "Nob Hill",
        "Presidio",
        "Marina District",
        "Pacific Heights",
        "Golden Gate Park",
        "Chinatown",
        "Richmond District",
    ]

    # Travel times (minutes)
    travel = {loc: {} for loc in L}
    def set_travel(frm, to, t):
        travel[frm][to] = t

    # Fill travel times from the problem
    set_travel("Mission District", "The Castro", 7)
    set_travel("Mission District", "Nob Hill", 12)
    set_travel("Mission District", "Presidio", 25)
    set_travel("Mission District", "Marina District", 19)
    set_travel("Mission District", "Pacific Heights", 16)
    set_travel("Mission District", "Golden Gate Park", 17)
    set_travel("Mission District", "Chinatown", 16)
    set_travel("Mission District", "Richmond District", 20)

    set_travel("The Castro", "Mission District", 7)
    set_travel("The Castro", "Nob Hill", 16)
    set_travel("The Castro", "Presidio", 20)
    set_travel("The Castro", "Marina District", 21)
    set_travel("The Castro", "Pacific Heights", 16)
    set_travel("The Castro", "Golden Gate Park", 11)
    set_travel("The Castro", "Chinatown", 22)
    set_travel("The Castro", "Richmond District", 16)

    set_travel("Nob Hill", "Mission District", 13)
    set_travel("Nob Hill", "The Castro", 17)
    set_travel("Nob Hill", "Presidio", 17)
    set_travel("Nob Hill", "Marina District", 11)
    set_travel("Nob Hill", "Pacific Heights", 8)
    set_travel("Nob Hill", "Golden Gate Park", 17)
    set_travel("Nob Hill", "Chinatown", 6)
    set_travel("Nob Hill", "Richmond District", 14)

    set_travel("Presidio", "Mission District", 26)
    set_travel("Presidio", "The Castro", 21)
    set_travel("Presidio", "Nob Hill", 18)
    set_travel("Presidio", "Marina District", 11)
    set_travel("Presidio", "Pacific Heights", 11)
    set_travel("Presidio", "Golden Gate Park", 12)
    set_travel("Presidio", "Chinatown", 21)
    set_travel("Presidio", "Richmond District", 7)

    set_travel("Marina District", "Mission District", 20)
    set_travel("Marina District", "The Castro", 22)
    set_travel("Marina District", "Nob Hill", 12)
    set_travel("Marina District", "Presidio", 10)
    set_travel("Marina District", "Pacific Heights", 7)
    set_travel("Marina District", "Golden Gate Park", 18)
    set_travel("Marina District", "Chinatown", 15)
    set_travel("Marina District", "Richmond District", 11)

    set_travel("Pacific Heights", "Mission District", 15)
    set_travel("Pacific Heights", "The Castro", 16)
    set_travel("Pacific Heights", "Nob Hill", 8)
    set_travel("Pacific Heights", "Presidio", 11)
    set_travel("Pacific Heights", "Marina District", 6)
    set_travel("Pacific Heights", "Golden Gate Park", 15)
    set_travel("Pacific Heights", "Chinatown", 11)
    set_travel("Pacific Heights", "Richmond District", 12)

    set_travel("Golden Gate Park", "Mission District", 17)
    set_travel("Golden Gate Park", "The Castro", 13)
    set_travel("Golden Gate Park", "Nob Hill", 20)
    set_travel("Golden Gate Park", "Presidio", 11)
    set_travel("Golden Gate Park", "Marina District", 16)
    set_travel("Golden Gate Park", "Pacific Heights", 16)
    set_travel("Golden Gate Park", "Chinatown", 23)
    set_travel("Golden Gate Park", "Richmond District", 7)

    set_travel("Chinatown", "Mission District", 17)
    set_travel("Chinatown", "The Castro", 22)
    set_travel("Chinatown", "Nob Hill", 9)
    set_travel("Chinatown", "Presidio", 19)
    set_travel("Chinatown", "Marina District", 12)
    set_travel("Chinatown", "Pacific Heights", 10)
    set_travel("Chinatown", "Golden Gate Park", 23)
    set_travel("Chinatown", "Richmond District", 20)

    set_travel("Richmond District", "Mission District", 20)
    set_travel("Richmond District", "The Castro", 16)
    set_travel("Richmond District", "Nob Hill", 17)
    set_travel("Richmond District", "Presidio", 7)
    set_travel("Richmond District", "Marina District", 9)
    set_travel("Richmond District", "Pacific Heights", 10)
    set_travel("Richmond District", "Golden Gate Park", 9)
    set_travel("Richmond District", "Chinatown", 20)

    # Add zero travel for same location
    for a in L:
        travel[a][a] = 0

    # People and constraints
    people = [
        {
            "name": "Lisa",
            "location": "The Castro",
            "start": minutes(19, 15),
            "end": minutes(21, 15),
            "min_duration": 120,
        },
        {
            "name": "Daniel",
            "location": "Nob Hill",
            "start": minutes(8, 15),
            "end": minutes(11, 0),
            "min_duration": 15,
        },
        {
            "name": "Elizabeth",
            "location": "Presidio",
            "start": minutes(21, 15),
            "end": minutes(22, 15),
            "min_duration": 45,
        },
        {
            "name": "Steven",
            "location": "Marina District",
            "start": minutes(16, 30),
            "end": minutes(20, 45),
            "min_duration": 90,
        },
        {
            "name": "Timothy",
            "location": "Pacific Heights",
            "start": minutes(12, 0),
            "end": minutes(18, 0),
            "min_duration": 90,
        },
        {
            "name": "Ashley",
            "location": "Golden Gate Park",
            "start": minutes(20, 45),
            "end": minutes(21, 45),
            "min_duration": 60,
        },
        {
            "name": "Kevin",
            "location": "Chinatown",
            "start": minutes(12, 0),
            "end": minutes(19, 0),
            "min_duration": 30,
        },
        {
            "name": "Betty",
            "location": "Richmond District",
            "start": minutes(13, 15),
            "end": minutes(15, 45),
            "min_duration": 30,
        },
    ]

    # Start conditions
    day_start_loc = "Mission District"
    day_start_time = minutes(9, 0)

    # SMT variables
    opt = Optimize()
    opt.set(priority='lex')

    vars_map = {}
    for p in people:
        s = Int(f"start_{p['name']}")
        e = Int(f"end_{p['name']}")
        meet = Bool(f"meet_{p['name']}")
        vars_map[p['name']] = {"start": s, "end": e, "meet": meet}
        # Domains
        opt.add(s >= 0, s <= 24 * 60)
        opt.add(e >= 0, e <= 24 * 60)
        opt.add(e >= s)

        # If meeting, must fit window, meet min duration, and be reachable from the day's start
        opt.add(Implies(
            meet,
            And(
                s >= p["start"],
                e <= p["end"],
                e - s >= p["min_duration"],
                s >= day_start_time + travel[day_start_loc][p["location"]],
            )
        ))
        # If not meeting, collapse times to window start (for determinism)
        opt.add(Implies(
            Not(meet),
            And(s == p["start"], e == p["start"])
        ))

    # Pairwise non-overlap and travel feasibility between meetings
    for i in range(len(people)):
        for j in range(i + 1, len(people)):
            pi = people[i]
            pj = people[j]
            vi = vars_map[pi["name"]]
            vj = vars_map[pj["name"]]
            ti = travel[pi["location"]][pj["location"]]
            tj = travel[pj["location"]][pi["location"]]
            opt.add(Implies(
                And(vi["meet"], vj["meet"]),
                Or(
                    vi["end"] + ti <= vj["start"],
                    vj["end"] + tj <= vi["start"]
                )
            ))

    # Objective 1: maximize number of meetings
    total_meetings = Sum([If(vars_map[p["name"]]["meet"], 1, 0) for p in people])
    opt.maximize(total_meetings)

    # Objective 2: maximize total meeting time (lexicographic tie-breaker)
    total_minutes = Sum([If(vars_map[p["name"]]["meet"], vars_map[p["name"]]["end"] - vars_map[p["name"]]["start"], 0) for p in people])
    opt.maximize(total_minutes)

    # Solve
    if opt.check() != sat:
        result = {"itinerary": []}
        print(json.dumps(result))
        return

    m = opt.model()

    # Collect meetings
    events = []
    for p in people:
        vp = vars_map[p["name"]]
        if m.eval(vp["meet"], model_completion=True):
            s = m.eval(vp["start"]).as_long()
            e = m.eval(vp["end"]).as_long()
            events.append({
                "action": "meet",
                "location": p["location"],
                "person": p["name"],
                "start": to_hhmm(s),
                "end": to_hhmm(e),
                "_start_mins": s  # for sorting
            })

    # Sort by start time
    events.sort(key=lambda x: x["_start_mins"])
    for ev in events:
        ev.pop("_start_mins", None)

    print(json.dumps({"itinerary": events}, ensure_ascii=False))

if __name__ == "__main__":
    main()