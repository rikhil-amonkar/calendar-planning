import json
from z3 import *

def parse_time_12h(t):
    t = t.strip().upper()
    # Expect formats like "8:45PM", "10:00AM", "7:30AM"
    if t.endswith("AM"):
        ampm = "AM"
    elif t.endswith("PM"):
        ampm = "PM"
    else:
        raise ValueError("Time must end with AM or PM")
    t = t[:-2]
    if ":" in t:
        h_str, m_str = t.split(":")
        h = int(h_str)
        m = int(m_str)
    else:
        h = int(t)
        m = 0
    if ampm == "AM":
        if h == 12:
            h = 0
    else:
        if h != 12:
            h += 12
    return h * 60 + m

def format_24h(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Locations
Sunset = "Sunset District"
RussianHill = "Russian Hill"
TheCastro = "The Castro"
Richmond = "Richmond District"
Marina = "Marina District"
NorthBeach = "North Beach"
UnionSquare = "Union Square"
GoldenGatePark = "Golden Gate Park"

locations = [Sunset, RussianHill, TheCastro, Richmond, Marina, NorthBeach, UnionSquare, GoldenGatePark]

# Travel times (minutes)
travel = {
    (Sunset, RussianHill): 24,
    (Sunset, TheCastro): 17,
    (Sunset, Richmond): 12,
    (Sunset, Marina): 21,
    (Sunset, NorthBeach): 29,
    (Sunset, UnionSquare): 30,
    (Sunset, GoldenGatePark): 11,

    (RussianHill, Sunset): 23,
    (RussianHill, TheCastro): 21,
    (RussianHill, Richmond): 14,
    (RussianHill, Marina): 7,
    (RussianHill, NorthBeach): 5,
    (RussianHill, UnionSquare): 11,
    (RussianHill, GoldenGatePark): 21,

    (TheCastro, Sunset): 17,
    (TheCastro, RussianHill): 18,
    (TheCastro, Richmond): 16,
    (TheCastro, Marina): 21,
    (TheCastro, NorthBeach): 20,
    (TheCastro, UnionSquare): 19,
    (TheCastro, GoldenGatePark): 11,

    (Richmond, Sunset): 11,
    (Richmond, RussianHill): 13,
    (Richmond, TheCastro): 16,
    (Richmond, Marina): 9,
    (Richmond, NorthBeach): 17,
    (Richmond, UnionSquare): 21,
    (Richmond, GoldenGatePark): 9,

    (Marina, Sunset): 19,
    (Marina, RussianHill): 8,
    (Marina, TheCastro): 22,
    (Marina, Richmond): 11,
    (Marina, NorthBeach): 11,
    (Marina, UnionSquare): 16,
    (Marina, GoldenGatePark): 18,

    (NorthBeach, Sunset): 27,
    (NorthBeach, RussianHill): 4,
    (NorthBeach, TheCastro): 22,
    (NorthBeach, Richmond): 18,
    (NorthBeach, Marina): 9,
    (NorthBeach, UnionSquare): 7,
    (NorthBeach, GoldenGatePark): 22,

    (UnionSquare, Sunset): 26,
    (UnionSquare, RussianHill): 13,
    (UnionSquare, TheCastro): 19,
    (UnionSquare, Richmond): 20,
    (UnionSquare, Marina): 18,
    (UnionSquare, NorthBeach): 10,
    (UnionSquare, GoldenGatePark): 22,

    (GoldenGatePark, Sunset): 10,
    (GoldenGatePark, RussianHill): 19,
    (GoldenGatePark, TheCastro): 13,
    (GoldenGatePark, Richmond): 7,
    (GoldenGatePark, Marina): 16,
    (GoldenGatePark, NorthBeach): 24,
    (GoldenGatePark, UnionSquare): 22
}

# Friends with availability and minimum meeting durations
friends = {
    "Karen": {
        "location": RussianHill,
        "window_start": parse_time_12h("8:45PM"),
        "window_end": parse_time_12h("9:45PM"),
        "min_duration": 60
    },
    "Jessica": {
        "location": TheCastro,
        "window_start": parse_time_12h("3:45PM"),
        "window_end": parse_time_12h("7:30PM"),
        "min_duration": 60
    },
    "Matthew": {
        "location": Richmond,
        "window_start": parse_time_12h("7:30AM"),
        "window_end": parse_time_12h("3:15PM"),
        "min_duration": 15
    },
    "Michelle": {
        "location": Marina,
        "window_start": parse_time_12h("10:30AM"),
        "window_end": parse_time_12h("6:45PM"),
        "min_duration": 75
    },
    "Carol": {
        "location": NorthBeach,
        "window_start": parse_time_12h("12:00PM"),
        "window_end": parse_time_12h("5:00PM"),
        "min_duration": 90
    },
    "Stephanie": {
        "location": UnionSquare,
        "window_start": parse_time_12h("10:45AM"),
        "window_end": parse_time_12h("2:15PM"),
        "min_duration": 30
    },
    "Linda": {
        "location": GoldenGatePark,
        "window_start": parse_time_12h("10:45AM"),
        "window_end": parse_time_12h("10:00PM"),
        "min_duration": 90
    }
}

arrival_location = Sunset
arrival_time = parse_time_12h("9:00AM")

# Z3 Model
opt = Optimize()

# Variables
start = {}
end = {}
chosen = {}

# Helper sanitize for variable names
def varname(s):
    return s.replace(" ", "_")

for person, data in friends.items():
    start[person] = Int(f"start_{varname(person)}")
    end[person] = Int(f"end_{varname(person)}")
    chosen[person] = Bool(f"chosen_{varname(person)}")

    ws = data["window_start"]
    we = data["window_end"]
    min_dur = data["min_duration"]
    loc = data["location"]

    # Bounds for all times
    opt.add(start[person] >= 0, start[person] <= 24*60)
    opt.add(end[person] >= 0, end[person] <= 24*60)

    # If chosen, meeting must respect availability and minimum duration
    opt.add(Implies(chosen[person],
                    And(start[person] >= ws,
                        end[person] <= we,
                        end[person] - start[person] >= min_dur)))

    # If not chosen, collapse to window start (keeps variables benign)
    opt.add(Implies(Not(chosen[person]),
                    And(start[person] == ws, end[person] == ws)))

    # Start must be reachable from arrival at Sunset at 9:00
    # Only enforce if chosen
    origin_to_loc = travel[(arrival_location, loc)]
    opt.add(Implies(chosen[person], start[person] >= arrival_time + origin_to_loc))

# Pairwise ordering constraints with travel times
people = list(friends.keys())
for i in range(len(people)):
    for j in range(i+1, len(people)):
        p = people[i]
        q = people[j]
        loc_p = friends[p]["location"]
        loc_q = friends[q]["location"]
        b = Bool(f"order_{varname(p)}_before_{varname(q)}")
        # If both chosen and b is True, p before q with travel time
        opt.add(Implies(And(chosen[p], chosen[q], b),
                        start[q] >= end[p] + travel[(loc_p, loc_q)]))
        # If both chosen and b is False, q before p with travel time
        opt.add(Implies(And(chosen[p], chosen[q], Not(b)),
                        start[p] >= end[q] + travel[(loc_q, loc_p)]))

# Define final_end for secondary optimization
final_end = Int("final_end")
opt.add(final_end >= 0, final_end <= 24*60)
for person in people:
    opt.add(final_end >= end[person])

# Objectives: maximize number of meetings, then minimize finish time, then minimize total meeting time (prefer minimum durations)
count = Sum([If(chosen[p], 1, 0) for p in people])
dur_sum = Sum([If(chosen[p], end[p] - start[p], 0) for p in people])

opt.maximize(count)
opt.minimize(final_end)
opt.minimize(dur_sum)

# Solve
if opt.check() != sat:
    # If unsat (shouldn't happen), output empty itinerary
    result = {"itinerary": []}
    print(json.dumps(result))
else:
    m = opt.model()
    schedule = []
    for person in people:
        if is_true(m.evaluate(chosen[person])):
            st = m.evaluate(start[person]).as_long()
            et = m.evaluate(end[person]).as_long()
            schedule.append({
                "person": person,
                "location": friends[person]["location"],
                "start": st,
                "end": et
            })
    # Sort by start time
    schedule.sort(key=lambda x: x["start"])

    itinerary = []
    for item in schedule:
        itinerary.append({
            "action": "meet",
            "location": item["location"],
            "person": item["person"],
            "start_time": format_24h(item["start"]),
            "end_time": format_24h(item["end"])
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))