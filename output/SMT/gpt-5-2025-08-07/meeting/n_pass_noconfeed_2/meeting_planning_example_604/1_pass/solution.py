import json
from z3 import *

def parse_time(tstr):
    h, m = tstr.split(":")
    return int(h) * 60 + int(m)

def minutes_to_str(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

def build_distances():
    # Nested dict distances[from][to] = minutes
    d = {}
    def add(frm, to, minutes):
        d.setdefault(frm, {})[to] = minutes
    add("Fisherman's Wharf", "The Castro", 26)
    add("Fisherman's Wharf", "Golden Gate Park", 25)
    add("Fisherman's Wharf", "Embarcadero", 8)
    add("Fisherman's Wharf", "Russian Hill", 7)
    add("Fisherman's Wharf", "Nob Hill", 11)
    add("Fisherman's Wharf", "Alamo Square", 20)
    add("Fisherman's Wharf", "North Beach", 6)

    add("The Castro", "Fisherman's Wharf", 24)
    add("The Castro", "Golden Gate Park", 11)
    add("The Castro", "Embarcadero", 22)
    add("The Castro", "Russian Hill", 18)
    add("The Castro", "Nob Hill", 16)
    add("The Castro", "Alamo Square", 8)
    add("The Castro", "North Beach", 20)

    add("Golden Gate Park", "Fisherman's Wharf", 24)
    add("Golden Gate Park", "The Castro", 13)
    add("Golden Gate Park", "Embarcadero", 25)
    add("Golden Gate Park", "Russian Hill", 19)
    add("Golden Gate Park", "Nob Hill", 20)
    add("Golden Gate Park", "Alamo Square", 10)
    add("Golden Gate Park", "North Beach", 24)

    add("Embarcadero", "Fisherman's Wharf", 6)
    add("Embarcadero", "The Castro", 25)
    add("Embarcadero", "Golden Gate Park", 25)
    add("Embarcadero", "Russian Hill", 8)
    add("Embarcadero", "Nob Hill", 10)
    add("Embarcadero", "Alamo Square", 19)
    add("Embarcadero", "North Beach", 5)

    add("Russian Hill", "Fisherman's Wharf", 7)
    add("Russian Hill", "The Castro", 21)
    add("Russian Hill", "Golden Gate Park", 21)
    add("Russian Hill", "Embarcadero", 8)
    add("Russian Hill", "Nob Hill", 5)
    add("Russian Hill", "Alamo Square", 15)
    add("Russian Hill", "North Beach", 5)

    add("Nob Hill", "Fisherman's Wharf", 11)
    add("Nob Hill", "The Castro", 17)
    add("Nob Hill", "Golden Gate Park", 17)
    add("Nob Hill", "Embarcadero", 9)
    add("Nob Hill", "Russian Hill", 5)
    add("Nob Hill", "Alamo Square", 11)
    add("Nob Hill", "North Beach", 8)

    add("Alamo Square", "Fisherman's Wharf", 19)
    add("Alamo Square", "The Castro", 8)
    add("Alamo Square", "Golden Gate Park", 9)
    add("Alamo Square", "Embarcadero", 17)
    add("Alamo Square", "Russian Hill", 13)
    add("Alamo Square", "Nob Hill", 11)
    add("Alamo Square", "North Beach", 15)

    add("North Beach", "Fisherman's Wharf", 5)
    add("North Beach", "The Castro", 22)
    add("North Beach", "Golden Gate Park", 22)
    add("North Beach", "Embarcadero", 6)
    add("North Beach", "Russian Hill", 4)
    add("North Beach", "Nob Hill", 7)
    add("North Beach", "Alamo Square", 16)

    return d

def main():
    START_LOCATION = "Fisherman's Wharf"
    ARRIVAL_TIME = parse_time("9:00")  # 9:00 at Fisherman's Wharf

    # Friends, their locations, availability windows, and minimum durations
    friends = [
        {"person": "Laura", "location": "The Castro", "start": "19:45", "end": "21:30", "min_minutes": 105},
        {"person": "Daniel", "location": "Golden Gate Park", "start": "21:15", "end": "21:45", "min_minutes": 15},
        {"person": "William", "location": "Embarcadero", "start": "7:00", "end": "9:00", "min_minutes": 90},
        {"person": "Karen", "location": "Russian Hill", "start": "14:30", "end": "19:45", "min_minutes": 30},
        {"person": "Stephanie", "location": "Nob Hill", "start": "7:30", "end": "9:30", "min_minutes": 45},
        {"person": "Joseph", "location": "Alamo Square", "start": "11:30", "end": "12:45", "min_minutes": 15},
        {"person": "Kimberly", "location": "North Beach", "start": "15:45", "end": "19:15", "min_minutes": 30},
    ]

    # Preprocess times
    for f in friends:
        f["start_min"] = parse_time(f["start"])
        f["end_min"] = parse_time(f["end"])

    # Distances
    dist = build_distances()

    def travel(a, b):
        return dist[a][b]

    # Z3 variables
    opt = Optimize()
    n = len(friends)
    meet_vars = []
    start_vars = []
    end_vars = []

    for i, f in enumerate(friends):
        meet = Bool(f"meet_{i}")
        s = Int(f"start_{i}")
        e = Int(f"end_{i}")
        meet_vars.append(meet)
        start_vars.append(s)
        end_vars.append(e)

        # Domains
        opt.add(s >= 0, s <= 24*60)
        opt.add(e >= 0, e <= 24*60)

        # If meeting, respect availability, minimum duration, and baseline travel from starting location
        opt.add(Implies(meet, s >= f["start_min"]))
        opt.add(Implies(meet, e <= f["end_min"]))
        opt.add(Implies(meet, e > s))
        opt.add(Implies(meet, e - s >= f["min_minutes"]))
        # Baseline: cannot arrive before traveling from starting location at 9:00
        opt.add(Implies(meet, s >= ARRIVAL_TIME + travel(START_LOCATION, f["location"])))
        # If not meeting, no duration
        opt.add(Implies(Not(meet), e == s))

    # Pairwise non-overlap with travel-time precedence disjunction
    for i in range(n):
        for j in range(i+1, n):
            li = friends[i]["location"]
            lj = friends[j]["location"]
            tij = travel(li, lj)
            tji = travel(lj, li)
            # If both meetings happen, then either i before j with travel, or j before i with travel
            opt.add(Implies(And(meet_vars[i], meet_vars[j]),
                            Or(end_vars[i] + tij <= start_vars[j],
                               end_vars[j] + tji <= start_vars[i])))

    # Objectives:
    # 1) Maximize number of people met
    meet_count = Sum([If(meet_vars[i], 1, 0) for i in range(n)])
    opt.maximize(meet_count)

    # 2) Maximize total meeting minutes
    total_meeting_minutes = Sum([If(meet_vars[i], end_vars[i] - start_vars[i], 0) for i in range(n)])
    opt.maximize(total_meeting_minutes)

    # Solve
    if opt.check() != sat:
        print(json.dumps({"itinerary": []}))
        return

    model = opt.model()

    # Extract solution
    itinerary = []
    for i, f in enumerate(friends):
        if is_true(model.evaluate(meet_vars[i], model_completion=True)):
            s = model.evaluate(start_vars[i], model_completion=True).as_long()
            e = model.evaluate(end_vars[i], model_completion=True).as_long()
            itinerary.append({
                "action": "meet",
                "location": f["location"],
                "person": f["person"],
                "start_time": minutes_to_str(s),
                "end_time": minutes_to_str(e)
            })

    # Sort by start time
    itinerary.sort(key=lambda x: parse_time(x["start_time"]))

    result = {"itinerary": itinerary}
    print("SOLUTION:")
    print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    main()