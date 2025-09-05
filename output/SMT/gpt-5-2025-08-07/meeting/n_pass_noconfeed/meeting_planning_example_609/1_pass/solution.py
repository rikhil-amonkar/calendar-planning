import json
from z3 import Int, Bool, If, And, Or, Optimize, sat

def minutes_to_str(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

def build_travel():
    t = {}
    locations = [
        "Chinatown",
        "Mission District",
        "Alamo Square",
        "Pacific Heights",
        "Union Square",
        "Golden Gate Park",
        "Sunset District",
        "Presidio",
    ]
    for loc in locations:
        t[loc] = {}
    # Fill directed travel times (in minutes)
    t["Chinatown"]["Mission District"] = 18
    t["Chinatown"]["Alamo Square"] = 17
    t["Chinatown"]["Pacific Heights"] = 10
    t["Chinatown"]["Union Square"] = 7
    t["Chinatown"]["Golden Gate Park"] = 23
    t["Chinatown"]["Sunset District"] = 29
    t["Chinatown"]["Presidio"] = 19

    t["Mission District"]["Chinatown"] = 16
    t["Mission District"]["Alamo Square"] = 11
    t["Mission District"]["Pacific Heights"] = 16
    t["Mission District"]["Union Square"] = 15
    t["Mission District"]["Golden Gate Park"] = 17
    t["Mission District"]["Sunset District"] = 24
    t["Mission District"]["Presidio"] = 25

    t["Alamo Square"]["Chinatown"] = 16
    t["Alamo Square"]["Mission District"] = 10
    t["Alamo Square"]["Pacific Heights"] = 10
    t["Alamo Square"]["Union Square"] = 14
    t["Alamo Square"]["Golden Gate Park"] = 9
    t["Alamo Square"]["Sunset District"] = 16
    t["Alamo Square"]["Presidio"] = 18

    t["Pacific Heights"]["Chinatown"] = 11
    t["Pacific Heights"]["Mission District"] = 15
    t["Pacific Heights"]["Alamo Square"] = 10
    t["Pacific Heights"]["Union Square"] = 12
    t["Pacific Heights"]["Golden Gate Park"] = 15
    t["Pacific Heights"]["Sunset District"] = 21
    t["Pacific Heights"]["Presidio"] = 11

    t["Union Square"]["Chinatown"] = 7
    t["Union Square"]["Mission District"] = 14
    t["Union Square"]["Alamo Square"] = 15
    t["Union Square"]["Pacific Heights"] = 15
    t["Union Square"]["Golden Gate Park"] = 22
    t["Union Square"]["Sunset District"] = 26
    t["Union Square"]["Presidio"] = 24

    t["Golden Gate Park"]["Chinatown"] = 23
    t["Golden Gate Park"]["Mission District"] = 17
    t["Golden Gate Park"]["Alamo Square"] = 10
    t["Golden Gate Park"]["Pacific Heights"] = 16
    t["Golden Gate Park"]["Union Square"] = 22
    t["Golden Gate Park"]["Sunset District"] = 10
    t["Golden Gate Park"]["Presidio"] = 11

    t["Sunset District"]["Chinatown"] = 30
    t["Sunset District"]["Mission District"] = 24
    t["Sunset District"]["Alamo Square"] = 17
    t["Sunset District"]["Pacific Heights"] = 21
    t["Sunset District"]["Union Square"] = 30
    t["Sunset District"]["Golden Gate Park"] = 11
    t["Sunset District"]["Presidio"] = 16

    t["Presidio"]["Chinatown"] = 21
    t["Presidio"]["Mission District"] = 26
    t["Presidio"]["Alamo Square"] = 18
    t["Presidio"]["Pacific Heights"] = 11
    t["Presidio"]["Union Square"] = 22
    t["Presidio"]["Golden Gate Park"] = 12
    t["Presidio"]["Sunset District"] = 15

    # Self travel time as 0
    for a in t:
        t[a][a] = 0
    return t

def main():
    travel = build_travel()

    # Start conditions
    start_location = "Chinatown"
    start_time = 9 * 60  # 9:00 -> 540

    # People with availability windows (in minutes since 0:00) and minimum meeting durations (minutes)
    people = [
        {"name": "David",   "location": "Mission District",   "avail_start": 8*60,     "avail_end": 19*60+45, "min_dur": 45},
        {"name": "Kenneth", "location": "Alamo Square",       "avail_start": 14*60,    "avail_end": 19*60+45, "min_dur": 120},
        {"name": "John",    "location": "Pacific Heights",    "avail_start": 17*60,    "avail_end": 20*60,    "min_dur": 15},
        {"name": "Charles", "location": "Union Square",       "avail_start": 21*60+45, "avail_end": 22*60+45, "min_dur": 60},
        {"name": "Deborah", "location": "Golden Gate Park",   "avail_start": 7*60,     "avail_end": 18*60+15, "min_dur": 90},
        {"name": "Karen",   "location": "Sunset District",    "avail_start": 17*60+45, "avail_end": 21*60+15, "min_dur": 15},
        {"name": "Carol",   "location": "Presidio",           "avail_start": 8*60+15,  "avail_end": 9*60+15,  "min_dur": 30},
    ]

    # Z3 variables
    opt = Optimize()
    horizon = 24 * 60  # allow full day

    s_vars = {}
    e_vars = {}
    met_vars = {}

    for p in people:
        name = p["name"]
        s = Int(f"s_{name}")
        e = Int(f"e_{name}")
        met = Bool(f"met_{name}")
        s_vars[name] = s
        e_vars[name] = e
        met_vars[name] = met

        # Time bounds
        opt.add(s >= 0, s <= horizon, e >= 0, e <= horizon)

        # If met, enforce availability and duration; else no meeting duration
        a = p["avail_start"]
        b = p["avail_end"]
        min_dur = p["min_dur"]
        loc = p["location"]

        opt.add(
            If(
                met,
                And(
                    s >= a,
                    e <= b,
                    e - s >= min_dur
                ),
                And(
                    e == s  # if not met, collapse interval (kept within 0..horizon)
                )
            )
        )

        # Must be reachable from start (arrive at or after start + travel)
        # This lower bound ensures no meeting starts earlier than physically reachable from arrival point
        opt.add(
            If(
                met,
                s >= start_time + travel[start_location][loc],
                True
            )
        )

    # Pairwise non-overlap with travel, for every pair of met meetings
    for i in range(len(people)):
        for j in range(i+1, len(people)):
            pi = people[i]
            pj = people[j]
            ni = pi["name"]
            nj = pj["name"]
            li = pi["location"]
            lj = pj["location"]

            si = s_vars[ni]
            ei = e_vars[ni]
            sj = s_vars[nj]
            ej = e_vars[nj]
            mi = met_vars[ni]
            mj = met_vars[nj]

            tij = travel[li][lj]
            tji = travel[lj][li]

            # If both met, either i before j with travel, or j before i with travel
            opt.add(
                If(
                    And(mi, mj),
                    Or(
                        ei + tij <= sj,
                        ej + tji <= si
                    ),
                    True
                )
            )

    # Objective: maximize the number of friends met
    total_met = sum([If(met_vars[p["name"]], 1, 0) for p in people])
    opt.maximize(total_met)

    if opt.check() != sat:
        # If unsat (shouldn't happen), output empty itinerary
        output = {"itinerary": []}
        print(json.dumps(output))
        return

    model = opt.model()

    # Extract and sort meetings by start time
    meetings = []
    for p in people:
        name = p["name"]
        if model.eval(met_vars[name], model_completion=True) is True:
            s = model.eval(s_vars[name]).as_long()
            e = model.eval(e_vars[name]).as_long()
            meetings.append({
                "action": "meet",
                "location": p["location"],
                "person": name,
                "start": s,
                "end": e
            })

    meetings.sort(key=lambda m: m["start"])

    itinerary = []
    for m in meetings:
        itinerary.append({
            "action": "meet",
            "location": m["location"],
            "person": m["person"],
            "start_time": minutes_to_str(m["start"]),
            "end_time": minutes_to_str(m["end"]),
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()