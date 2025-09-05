import json
from z3 import Optimize, Int, Bool, And, Or, Not, Implies, If, Xor

# Helper functions
def parse_time(tstr):
    # tstr like '9:00', '13:30' in 24-hour
    h, m = tstr.split(":")
    return int(h) * 60 + int(m)

def minutes_to_time(m_rel_from_9):
    absolute = 9*60 + m_rel_from_9
    h = absolute // 60
    m = absolute % 60
    return f"{h}:{m:02d}"

# Locations
PRESIDIO = "Presidio"
locations = [
    PRESIDIO,
    "Richmond District",
    "North Beach",
    "Financial District",
    "Golden Gate Park",
    "Union Square",
]

# Travel times (minutes), as given
travel = {}
def set_t(a,b,t):
    travel[(a,b)] = t

# Presidio to others
set_t("Presidio", "Richmond District", 7)
set_t("Presidio", "North Beach", 18)
set_t("Presidio", "Financial District", 23)
set_t("Presidio", "Golden Gate Park", 12)
set_t("Presidio", "Union Square", 22)

# Richmond District to others
set_t("Richmond District", "Presidio", 7)
set_t("Richmond District", "North Beach", 17)
set_t("Richmond District", "Financial District", 22)
set_t("Richmond District", "Golden Gate Park", 9)
set_t("Richmond District", "Union Square", 21)

# North Beach to others
set_t("North Beach", "Presidio", 17)
set_t("North Beach", "Richmond District", 18)
set_t("North Beach", "Financial District", 8)
set_t("North Beach", "Golden Gate Park", 22)
set_t("North Beach", "Union Square", 7)

# Financial District to others
set_t("Financial District", "Presidio", 22)
set_t("Financial District", "Richmond District", 21)
set_t("Financial District", "North Beach", 7)
set_t("Financial District", "Golden Gate Park", 23)
set_t("Financial District", "Union Square", 9)

# Golden Gate Park to others
set_t("Golden Gate Park", "Presidio", 11)
set_t("Golden Gate Park", "Richmond District", 7)
set_t("Golden Gate Park", "North Beach", 24)
set_t("Golden Gate Park", "Financial District", 26)
set_t("Golden Gate Park", "Union Square", 22)

# Union Square to others
set_t("Union Square", "Presidio", 24)
set_t("Union Square", "Richmond District", 20)
set_t("Union Square", "North Beach", 10)
set_t("Union Square", "Financial District", 9)
set_t("Union Square", "Golden Gate Park", 22)

# People and constraints
people = [
    {
        "name": "Jason",
        "location": "Richmond District",
        "avail_start": "13:00",
        "avail_end": "20:45",
        "min_duration": 90
    },
    {
        "name": "Melissa",
        "location": "North Beach",
        "avail_start": "18:45",
        "avail_end": "20:15",
        "min_duration": 45
    },
    {
        "name": "Brian",
        "location": "Financial District",
        "avail_start": "9:45",
        "avail_end": "21:45",
        "min_duration": 15
    },
    {
        "name": "Elizabeth",
        "location": "Golden Gate Park",
        "avail_start": "8:45",
        "avail_end": "21:30",
        "min_duration": 105
    },
    {
        "name": "Laura",
        "location": "Union Square",
        "avail_start": "14:15",
        "avail_end": "19:30",
        "min_duration": 75
    }
]

# Convert availability to minutes relative to 9:00
base = parse_time("9:00")
for p in people:
    st = parse_time(p["avail_start"]) - base
    en = parse_time(p["avail_end"]) - base
    # Can't start before arrival to the city at 9:00 (minute 0)
    p["rel_start"] = max(0, st)
    p["rel_end"] = en

# Z3 model
opt = Optimize()
opt.set(priority='lex')

# Horizon - safe upper bound after 9:00, latest relevant end is 21:45 -> 12h45 = 765
HORIZON = 900

# Variables
start = {}
end = {}
meet = {}
index_by_name = {}
for i, p in enumerate(people):
    index_by_name[p["name"]] = i
    start[i] = Int(f"start_{i}")
    end[i] = Int(f"end_{i}")
    meet[i] = Bool(f"meet_{i}")
    # Domain constraints
    opt.add(start[i] >= 0, start[i] <= HORIZON)
    opt.add(end[i] >= 0, end[i] <= HORIZON)
    # Availability constraints when meeting
    opt.add(Implies(meet[i],
                    And(start[i] >= p["rel_start"],
                        end[i] <= p["rel_end"],
                        end[i] - start[i] >= p["min_duration"])))


# Precedence booleans for all ordered pairs
before = {}
n = len(people)
for i in range(n):
    for j in range(n):
        if i == j:
            continue
        before[(i,j)] = Bool(f"before_{i}_{j}")
        # If either meeting is not happening, no ordering
        opt.add(Implies(Not(And(meet[i], meet[j])), And(Not(before[(i,j)]))))
# Pairwise XOR and timing constraints
for i in range(n):
    for j in range(i+1, n):
        # If both met -> exactly one ordering holds
        opt.add(Implies(And(meet[i], meet[j]), Xor(before[(i,j)], before[(j,i)])))
        # If not both met -> both orderings false (already ensured above)
        # Temporal constraints when ordering holds
        li = people[i]["location"]
        lj = people[j]["location"]
        tij = travel[(li, lj)]
        tji = travel[(lj, li)]
        opt.add(Implies(before[(i,j)], And(meet[i], meet[j], start[j] >= end[i] + tij)))
        opt.add(Implies(before[(j,i)], And(meet[i], meet[j], start[i] >= end[j] + tji)))

# First-meeting reachability from Presidio:
for i in range(n):
    loc_i = people[i]["location"]
    from_start = travel[(PRESIDIO, loc_i)]
    preds = [before[(j,i)] for j in range(n) if j != i]
    # If meeting person i, then either someone is scheduled before them,
    # or they are the first and must respect travel time from Presidio.
    opt.add(Implies(meet[i], Or(*(preds + [start[i] >= from_start]))))

# Objectives:
# 1) Maximize number of friends met
obj1 = sum([If(meet[i], 1, 0) for i in range(n)])
# 2) Maximize total meeting time
obj2 = sum([If(meet[i], end[i] - start[i], 0) for i in range(n)])

opt.maximize(obj1)
opt.maximize(obj2)

# Solve
if opt.check().r == 1:
    model = opt.model()
    itinerary = []
    meetings = []
    for i, p in enumerate(people):
        if model.evaluate(meet[i], model_completion=True):
            s = int(model.evaluate(start[i]).as_long())
            e = int(model.evaluate(end[i]).as_long())
            meetings.append((s, e, p["location"], p["name"]))
    # Sort by start time
    meetings.sort(key=lambda x: x[0])
    for s, e, loc, name in meetings:
        itinerary.append({
            "action": "meet",
            "location": loc,
            "person": name,
            "start_time": minutes_to_time(s),
            "end_time": minutes_to_time(e)
        })
    result = {"itinerary": itinerary}
else:
    result = {"itinerary": []}

print(json.dumps(result, ensure_ascii=False))