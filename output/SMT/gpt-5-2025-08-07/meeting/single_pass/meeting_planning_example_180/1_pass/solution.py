# Z3-based scheduler for meeting friends in San Francisco
# Objective: maximize number of friends met (subject to travel and availability),
# then maximize total meeting time.

from z3 import Int, Bool, Optimize, If, And, Or, Implies

def to_minutes(hh, mm):
    return hh*60 + mm

def fmt_hhmm(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

# Locations
NB = "North Beach"
MD = "Mission District"
TC = "The Castro"

# Travel times (minutes), directional
travel = {
    (NB, MD): 18,
    (NB, TC): 22,
    (MD, NB): 17,
    (MD, TC): 7,
    (TC, NB): 20,
    (TC, MD): 7,
}

# Start of day arrival
arrive_loc = NB
arrive_time = to_minutes(9, 0)

# Friends data
friends = {
    "James": {
        "loc": MD,
        "avail_start": to_minutes(12, 45),
        "avail_end": to_minutes(14, 0),
        "min_dur": 75,
    },
    "Robert": {
        "loc": TC,
        "avail_start": to_minutes(12, 45),
        "avail_end": to_minutes(15, 15),
        "min_dur": 30,
    },
}

# Build Z3 model
opt = Optimize()

# Variables per friend
vars_ = {}
for name, info in friends.items():
    s = Int(f"{name}_start")
    e = Int(f"{name}_end")
    meet = Bool(f"meet_{name}")
    # Reasonable bounds (within the day)
    opt.add(s >= 0, s <= 24*60, e >= 0, e <= 24*60)
    # Availability and duration constraints when meeting
    opt.add(Implies(meet, s >= info["avail_start"]))
    opt.add(Implies(meet, e <= info["avail_end"]))
    opt.add(Implies(meet, e >= s + info["min_dur"]))
    # If not meeting, keep end == start (zero duration) within some range
    opt.add(Implies(~meet, e == s))
    vars_[name] = (s, e, meet)

# Travel feasibility constraints
# Define helper to get travel time
def ttime(a, b):
    return travel[(a, b)]

# Extract variables
sJ, eJ, mJ = vars_["James"]
sR, eR, mR = vars_["Robert"]

# If both meetings are scheduled, they must be sequenceable with travel time
# Either James then Robert, or Robert then James
opt.add(Implies(And(mJ, mR),
                Or(
                    And(sJ >= arrive_time + ttime(arrive_loc, friends["James"]["loc"]),
                        sR >= eJ + ttime(friends["James"]["loc"], friends["Robert"]["loc"])),
                    And(sR >= arrive_time + ttime(arrive_loc, friends["Robert"]["loc"]),
                        sJ >= eR + ttime(friends["Robert"]["loc"], friends["James"]["loc"])),
                )))

# If only one meeting is scheduled, it must be reachable from arrival
opt.add(Implies(And(mJ, ~mR),
                sJ >= arrive_time + ttime(arrive_loc, friends["James"]["loc"])))
opt.add(Implies(And(~mJ, mR),
                sR >= arrive_time + ttime(arrive_loc, friends["Robert"]["loc"])))

# Objective: maximize number of friends met, then total meeting time
meet_count = If(mJ, 1, 0) + If(mR, 1, 0)
dur_total = If(mJ, eJ - sJ, 0) + If(mR, eR - sR, 0)

opt.maximize(meet_count)
opt.maximize(dur_total)

# Solve
assert opt.check() ==  sat
model = opt.model()

schedule = []
for name in friends:
    s, e, meet = vars_[name]
    if model.eval(meet).is_true():
        schedule.append((int(model.eval(s).as_long()), int(model.eval(e).as_long()), name))

# Sort by start time
schedule.sort(key=lambda x: x[0])

# Build the JSON-like itinerary dict
itinerary = []
for s, e, name in schedule:
    entry = {
        "action": "meet",
        "person": name,
        "start_time": fmt_hhmm(s),
        "end_time": fmt_hhmm(e),
    }
    itinerary.append(entry)

# Print the itinerary JSON
import json
print(json.dumps({"itinerary": itinerary}))