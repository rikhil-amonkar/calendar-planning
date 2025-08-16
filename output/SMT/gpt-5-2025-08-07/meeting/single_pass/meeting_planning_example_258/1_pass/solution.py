# Requires: z3-solver (pip install z3-solver)
from z3 import *
import json

def hm(h, m):
    return h * 60 + m

def fmt(mins):
    h = mins // 60
    m = mins % 60
    return f"{h:02d}:{m:02d}"

# Problem data
start_location = "Embarcadero"
day_start = hm(9, 0)

people = {
    "Betty": {
        "location": "Presidio",
        "avail_start": hm(10, 15),
        "avail_end": hm(21, 30),
        "min_duration": 45
    },
    "David": {
        "location": "Richmond District",
        "avail_start": hm(13, 0),
        "avail_end": hm(20, 15),
        "min_duration": 90
    },
    "Barbara": {
        "location": "Fisherman's Wharf",
        "avail_start": hm(9, 15),
        "avail_end": hm(20, 15),
        "min_duration": 120
    }
}

# Travel times (in minutes) between locations
travel = {
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Richmond District"): 18
}

names = list(people.keys())

opt = Optimize()
opt.set(priority='lex')  # Maximize count first, then minimize latest end

start_vars = {}
end_vars = {}
meet_vars = {}

# Create variables and constraints for each person
for n in names:
    s = Int(f"{n}_start")
    e = Int(f"{n}_end")
    m = Bool(f"{n}_meet")
    start_vars[n] = s
    end_vars[n] = e
    meet_vars[n] = m

    loc = people[n]["location"]
    avail_s = people[n]["avail_start"]
    avail_e = people[n]["avail_end"]
    min_dur = people[n]["min_duration"]

    # If meeting, must be within availability and meet minimum duration
    opt.add(Implies(m, And(s >= avail_s, e <= avail_e, e - s >= min_dur)))

    # If meeting, cannot start before you could arrive from the starting location at day_start
    opt.add(Implies(m, s >= day_start + travel[(start_location, loc)]))

    # Non-negativity and basic ordering
    opt.add(Implies(m, And(s >= 0, e >= 0, e >= s)))
    # If not meeting, collapse interval (keeps model tight, but not strictly necessary)
    opt.add(Implies(Not(m), e == s))

# Pairwise disjunctive scheduling with travel times
order_vars = {}
for i in range(len(names)):
    for j in range(i + 1, len(names)):
        ni, nj = names[i], names[j]
        oi_j = Bool(f"order_{ni}_before_{nj}")
        order_vars[(ni, nj)] = oi_j

        li, lj = people[ni]["location"], people[nj]["location"]
        ti_j = travel[(li, lj)]
        tj_i = travel[(lj, li)]

        si, ei = start_vars[ni], end_vars[ni]
        sj, ej = start_vars[nj], end_vars[nj]
        mi, mj = meet_vars[ni], meet_vars[nj]

        # If both are met, one must precede the other with appropriate travel time
        opt.add(Implies(And(mi, mj),
                        Or(And(oi_j, ei + ti_j <= sj),
                           And(Not(oi_j), ej + tj_i <= si))))
        # If one or both are not met, we don't constrain the order variable
        # (no extra constraints needed)

# Objective 1: maximize number of friends met
meet_count = Sum([If(meet_vars[n], IntVal(1), IntVal(0)) for n in names])
opt.maximize(meet_count)

# Objective 2: minimize latest end time among meetings (finish the 3 meetings as early as possible)
latest_end = Int("latest_end")
opt.add(latest_end >= day_start)
for n in names:
    opt.add(Implies(meet_vars[n], latest_end >= end_vars[n]))
opt.minimize(latest_end)

# Solve
if opt.check() != sat:
    raise RuntimeError("No feasible schedule found.")

model = opt.model()

# Build itinerary
meetings = []
for n in names:
    if is_true(model.evaluate(meet_vars[n], model_completion=True)):
        s = model.evaluate(start_vars[n]).as_long()
        e = model.evaluate(end_vars[n]).as_long()
        meetings.append({
            "action": "meet",
            "person": n,
            "start_min": s,
            "end_min": e
        })

# Sort by start time
meetings.sort(key=lambda x: x["start_min"])

# Format times
itinerary = []
for m in meetings:
    itinerary.append({
        "action": "meet",
        "person": m["person"],
        "start_time": fmt(m["start_min"]),
        "end_time": fmt(m["end_min"])
    })

# Print the resulting JSON itinerary
print(json.dumps({"itinerary": itinerary}, indent=2))