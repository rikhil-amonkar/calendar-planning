# Requires: z3-solver (pip install z3-solver)
from z3 import Optimize, Int, Bool, And, Or, Not, Implies, Xor, If, is_true
import json

def t(h, m):
    return h*60 + m

# Data
start_location = "Sunset District"
day_start = t(9, 0)

locations = [
    "Sunset District",
    "Russian Hill",
    "Chinatown",
    "Presidio",
    "Fisherman's Wharf"
]

travel = {
    "Sunset District": {
        "Russian Hill": 24,
        "Chinatown": 30,
        "Presidio": 16,
        "Fisherman's Wharf": 29
    },
    "Russian Hill": {
        "Sunset District": 23,
        "Chinatown": 9,
        "Presidio": 14,
        "Fisherman's Wharf": 7
    },
    "Chinatown": {
        "Sunset District": 29,
        "Russian Hill": 7,
        "Presidio": 19,
        "Fisherman's Wharf": 8
    },
    "Presidio": {
        "Sunset District": 15,
        "Russian Hill": 14,
        "Chinatown": 21,
        "Fisherman's Wharf": 19
    },
    "Fisherman's Wharf": {
        "Sunset District": 27,
        "Russian Hill": 7,
        "Chinatown": 12,
        "Presidio": 17
    }
}

persons = ["William", "Michelle", "George", "Robert"]
person_location = {
    "William": "Russian Hill",
    "Michelle": "Chinatown",
    "George": "Presidio",
    "Robert": "Fisherman's Wharf"
}
availability = {
    "William": (t(18,30), t(20,45)),
    "Michelle": (t(8,15), t(14,0)),
    "George":   (t(10,30), t(18,45)),
    "Robert":   (t(9,0), t(13,45))
}
min_meet = {
    "William": 105,
    "Michelle": 15,
    "George":   30,
    "Robert":   30
}

# Z3 model
opt = Optimize()

start = {p: Int(f"{p}_start") for p in persons}
end   = {p: Int(f"{p}_end")   for p in persons}
chosen= {p: Bool(f"{p}_chosen") for p in persons}

# Domain constraints
for p in persons:
    opt.add(start[p] >= 0, end[p] >= 0, start[p] <= 24*60, end[p] <= 24*60)
    s_av, e_av = availability[p]
    # If chosen: within availability, minimum duration exactly, and feasible from the start location
    opt.add(Implies(chosen[p], And(
        start[p] >= s_av,
        end[p] <= e_av,
        end[p] == start[p] + min_meet[p],
        start[p] >= day_start + travel[start_location][person_location[p]]
    )))
    # If not chosen: no time allocated
    opt.add(Implies(Not(chosen[p]), And(start[p] == 0, end[p] == 0)))

# Pairwise ordering and travel between meetings
order = {}
for i in range(len(persons)):
    for j in range(len(persons)):
        if i == j:
            continue
        a = persons[i]
        b = persons[j]
        order[(a,b)] = Bool(f"order_{a}_before_{b}")

# Ensure a total, consistent order among chosen meetings and enforce travel gaps
for i in range(len(persons)):
    for j in range(i+1, len(persons)):
        a = persons[i]
        b = persons[j]
        # Exactly one precedes the other if both are chosen
        opt.add(Implies(And(chosen[a], chosen[b]), Xor(order[(a,b)], order[(b,a)])))
        # Travel and non-overlap constraints, guarded by both chosen and the specific order
        opt.add(Implies(And(chosen[a], chosen[b], order[(a,b)]),
                        start[b] >= end[a] + travel[person_location[a]][person_location[b]]))
        opt.add(Implies(And(chosen[a], chosen[b], order[(b,a)]),
                        start[a] >= end[b] + travel[person_location[b]][person_location[a]]))

# Objectives: maximize number of friends met; tie-breaker minimize finish time of the last meeting
total_met = sum([If(chosen[p], 1, 0) for p in persons])
last_end = Int("last_end")
opt.add(last_end >= 0)
for p in persons:
    opt.add(last_end >= end[p])

opt.maximize(total_met)
opt.minimize(last_end)

res = opt.check()
if str(res) != "sat":
    print(json.dumps({"itinerary": []}))
    raise SystemExit

m = opt.model()

def fmt(mm):
    h = mm // 60
    mi = mm % 60
    return f"{h:02d}:{mi:02d}"

itinerary = []
# Collect chosen meetings
for p in persons:
    if is_true(m.evaluate(chosen[p])):
        s = m.evaluate(start[p]).as_long()
        e = m.evaluate(end[p]).as_long()
        itinerary.append((s, {
            "action": "meet",
            "person": p,
            "start_time": fmt(s),
            "end_time": fmt(e)
        }))

# Sort by start time
itinerary.sort(key=lambda x: x[0])
output = {"itinerary": [entry for _, entry in itinerary]}
print(json.dumps(output))