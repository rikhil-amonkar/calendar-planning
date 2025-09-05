# SOLUTION:
import json
from z3 import Optimize, Int, Bool, If, And, Or, Not, Sum

def to_minutes(s):
    h, m = s.split(":")
    return int(h) * 60 + int(m)

def to_hhmm(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Locations
E = "Embarcadero"
FWH = "Fisherman's Wharf"
FD = "Financial District"
RH = "Russian Hill"
MD = "Marina District"
RD = "Richmond District"
PH = "Pacific Heights"
HA = "Haight-Ashbury"
PR = "Presidio"
NH = "Nob Hill"
TC = "The Castro"

locations = [E, FWH, FD, RH, MD, RD, PH, HA, PR, NH, TC]

# Travel times (minutes)
travel = {
    (E, FWH): 6, (E, FD): 5, (E, RH): 8, (E, MD): 12, (E, RD): 21, (E, PH): 11, (E, HA): 21, (E, PR): 20, (E, NH): 10, (E, TC): 25,
    (FWH, E): 8, (FWH, FD): 11, (FWH, RH): 7, (FWH, MD): 9, (FWH, RD): 18, (FWH, PH): 12, (FWH, HA): 22, (FWH, PR): 17, (FWH, NH): 11, (FWH, TC): 27,
    (FD, E): 4, (FD, FWH): 10, (FD, RH): 11, (FD, MD): 15, (FD, RD): 21, (FD, PH): 13, (FD, HA): 19, (FD, PR): 22, (FD, NH): 8, (FD, TC): 20,
    (RH, E): 8, (RH, FWH): 7, (RH, FD): 11, (RH, MD): 7, (RH, RD): 14, (RH, PH): 7, (RH, HA): 17, (RH, PR): 14, (RH, NH): 5, (RH, TC): 21,
    (MD, E): 14, (MD, FWH): 10, (MD, FD): 17, (MD, RH): 8, (MD, RD): 11, (MD, PH): 7, (MD, HA): 16, (MD, PR): 10, (MD, NH): 12, (MD, TC): 22,
    (RD, E): 19, (RD, FWH): 18, (RD, FD): 22, (RD, RH): 13, (RD, MD): 9, (RD, PH): 10, (RD, HA): 10, (RD, PR): 7, (RD, NH): 17, (RD, TC): 16,
    (PH, E): 10, (PH, FWH): 13, (PH, FD): 13, (PH, RH): 7, (PH, MD): 6, (PH, RD): 12, (PH, HA): 11, (PH, PR): 11, (PH, NH): 8, (PH, TC): 16,
    (HA, E): 20, (HA, FWH): 23, (HA, FD): 21, (HA, RH): 17, (HA, MD): 17, (HA, RD): 10, (HA, PH): 12, (HA, PR): 15, (HA, NH): 15, (HA, TC): 6,
    (PR, E): 20, (PR, FWH): 19, (PR, FD): 23, (PR, RH): 14, (PR, MD): 11, (PR, RD): 7, (PR, PH): 11, (PR, HA): 15, (PR, NH): 18, (PR, TC): 21,
    (NH, E): 9, (NH, FWH): 10, (NH, FD): 9, (NH, RH): 5, (NH, MD): 11, (NH, RD): 14, (NH, PH): 8, (NH, HA): 13, (NH, PR): 17, (NH, TC): 17,
    (TC, E): 22, (TC, FWH): 24, (TC, FD): 21, (TC, RH): 18, (TC, MD): 21, (TC, RD): 16, (TC, PH): 16, (TC, HA): 6, (TC, PR): 20, (TC, NH): 16,
}

# Add zero travel time for staying in same location
for loc in locations:
    travel[(loc, loc)] = 0

# Friends and their constraints
friends = {
    "Stephanie": {"location": FWH, "start": "15:30", "end": "22:00", "min_dur": 30},
    "Lisa": {"location": FD, "start": "10:45", "end": "17:15", "min_dur": 15},
    "Melissa": {"location": RH, "start": "17:00", "end": "21:45", "min_dur": 120},
    "Betty": {"location": MD, "start": "10:45", "end": "14:15", "min_dur": 60},
    "Sarah": {"location": RD, "start": "16:15", "end": "19:30", "min_dur": 105},
    "Daniel": {"location": PH, "start": "18:30", "end": "21:45", "min_dur": 60},
    "Joshua": {"location": HA, "start": "9:00", "end": "15:30", "min_dur": 15},
    "Joseph": {"location": PR, "start": "7:00", "end": "13:00", "min_dur": 45},
    "Andrew": {"location": NH, "start": "19:45", "end": "22:00", "min_dur": 105},
    "John": {"location": TC, "start": "13:15", "end": "19:45", "min_dur": 45},
}

# Convert time strings to minutes and augment
for name, info in friends.items():
    info["start_min"] = to_minutes(info["start"])
    info["end_min"] = to_minutes(info["end"])

# Solver setup
opt = Optimize()
opt.set(priority='lex')

vars_start = {}
vars_dur = {}
vars_sel = {}

DAY_START = to_minutes("9:00")

for name, info in friends.items():
    s = Int(f"start_{name}")
    d = Int(f"dur_{name}")
    sel = Bool(f"sel_{name}")
    vars_start[name] = s
    vars_dur[name] = d
    vars_sel[name] = sel

    ws = info["start_min"]
    we = info["end_min"]
    mdur = info["min_dur"]

    # Bounds
    opt.add(s >= 0, s <= 24 * 60)
    opt.add(d >= 0, d <= 24 * 60)

    # If selected, must be within window and meet min duration
    opt.add(Implies(sel, And(
        s >= ws,
        s <= we - mdur,
        d >= mdur,
        s + d <= we
    )))
    # If not selected, no meeting duration
    opt.add(Implies(Not(sel), d == 0))

    # Reachability from initial location/time (weak but safe)
    opt.add(Implies(sel, s >= DAY_START + travel[(E, info["location"])]))

# Pairwise sequencing constraints with travel times
names = list(friends.keys())
for i in range(len(names)):
    for j in range(i + 1, len(names)):
        ni, nj = names[i], names[j]
        si, di, seli = vars_start[ni], vars_dur[ni], vars_sel[ni]
        sj, dj, selj = vars_start[nj], vars_dur[nj], vars_sel[nj]
        li = friends[ni]["location"]
        lj = friends[nj]["location"]
        tij = travel[(li, lj)]
        tji = travel[(lj, li)]
        opt.add(Implies(And(seli, selj),
                        Or(si + di + tij <= sj,
                           sj + dj + tji <= si)))

# Objective 1: maximize number of friends met
num_met = Sum([If(vars_sel[n], 1, 0) for n in names])
opt.maximize(num_met)

# Objective 2: maximize total meeting time
total_meeting_time = Sum([If(vars_sel[n], vars_dur[n], 0) for n in names])
opt.maximize(total_meeting_time)

# Solve
if opt.check() !=  sat:
    # Fallback: no solution (shouldn't happen with given data)
    print(json.dumps({"itinerary": []}))
else:
    model = opt.model()
    selected_meetings = []
    for name in names:
        if model.evaluate(vars_sel[name], model_completion=True):
            start_val = model.evaluate(vars_start[name], model_completion=True).as_long()
            dur_val = model.evaluate(vars_dur[name], model_completion=True).as_long()
            end_val = start_val + dur_val
            selected_meetings.append({
                "person": name,
                "location": friends[name]["location"],
                "start_min": start_val,
                "end_min": end_val
            })

    # Sort by start time
    selected_meetings.sort(key=lambda x: x["start_min"])

    itinerary = []
    for m in selected_meetings:
        itinerary.append({
            "action": "meet",
            "location": m["location"],
            "person": m["person"],
            "start_time": to_hhmm(m["start_min"]),
            "end_time": to_hhmm(m["end_min"])
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))