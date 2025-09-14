import json
from z3 import Optimize, Int, Bool, If, And, Or, Implies, Sum, is_true

# Helper functions
def time_to_minutes(h, m):
    return h * 60 + m

def minutes_to_str(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

# Locations
FD = "Financial District"
RH = "Russian Hill"
SD = "Sunset District"
NB = "North Beach"
CA = "The Castro"
GGP = "Golden Gate Park"

# Travel times in minutes (directed)
TT = {
    (FD, RH): 10, (FD, SD): 31, (FD, NB): 7,  (FD, CA): 23, (FD, GGP): 23,
    (RH, FD): 11, (RH, SD): 23, (RH, NB): 5,  (RH, CA): 21, (RH, GGP): 21,
    (SD, FD): 30, (SD, RH): 24, (SD, NB): 29, (SD, CA): 17, (SD, GGP): 11,
    (NB, FD): 8,  (NB, RH): 4,  (NB, SD): 27, (NB, CA): 22, (NB, GGP): 22,
    (CA, FD): 20, (CA, RH): 18, (CA, SD): 17, (CA, NB): 20, (CA, GGP): 11,
    (GGP, FD): 26, (GGP, RH): 19, (GGP, SD): 10, (GGP, NB): 24, (GGP, CA): 13,
}

def tt(l1, l2):
    return TT[(l1, l2)]

# Day bounds
DAY_START = time_to_minutes(9, 0)    # 9:00
DAY_END   = time_to_minutes(22, 0)   # 22:00

# People and constraints
people = [
    # name, location, (avail_start, avail_end), min_duration
    ("Patricia", SD,  (time_to_minutes(9, 15),  time_to_minutes(22, 0)), 60),
    ("Laura",    NB,  (time_to_minutes(12, 30), time_to_minutes(12, 45)), 15),
    ("Ronald",   RH,  (time_to_minutes(13, 45), time_to_minutes(17, 15)), 105),
    ("Mary",     GGP, (time_to_minutes(15, 0),  time_to_minutes(16, 30)), 60),
    ("Emily",    CA,  (time_to_minutes(16, 15), time_to_minutes(18, 30)), 60),
]

# Add a dummy "Start" node to encode initial location and start time
start_node = ("Start", FD, (DAY_START, DAY_START), 0)

# Combined list for variable allocation (Start is not a real meeting in output)
all_nodes = [start_node] + people

# Build Z3 optimizer
opt = Optimize()

# Z3 variables per node
meet = {}
start = {}
end = {}
dur = {}
pos = {}

# Create variables
for i, (name, loc, (a_start, a_end), min_dur) in enumerate(all_nodes):
    meet[name] = Bool(f"meet_{name}")
    start[name] = Int(f"start_{name}")
    end[name] = Int(f"end_{name}")
    dur[name] = Int(f"dur_{name}")
    pos[name] = Int(f"pos_{name}")

# Constraints for Start node: always "met" (used as anchor), fixed time at Financial District, pos=0
name, loc, (a_start, a_end), min_dur = start_node
opt.add(meet[name] == True)
opt.add(start[name] == a_start)
opt.add(end[name] == a_end)
opt.add(dur[name] == 0)
opt.add(pos[name] == 0)

# Constraints for real people
N = len(people)
for name, loc, (a_start, a_end), min_dur in people:
    # If met, respect availability, durations, and bounds; else set pos=0 and dur=0
    opt.add(Implies(meet[name],
                    And(start[name] >= a_start,
                        end[name] <= a_end,
                        start[name] >= DAY_START,
                        end[name] <= DAY_END,
                        dur[name] >= min_dur,
                        dur[name] <= (a_end - a_start),
                        end[name] == start[name] + dur[name],
                        pos[name] >= 1, pos[name] <= N)))
    opt.add(Implies(~meet[name], And(dur[name] == 0, pos[name] == 0)))
    # Also basic sanity bounds (optional when not met)
    opt.add(start[name] >= DAY_START)
    opt.add(end[name] <= DAY_END)

# Uniqueness of positions among met people
for i in range(len(people)):
    for j in range(i+1, len(people)):
        pi = people[i][0]
        pj = people[j][0]
        opt.add(Implies(And(meet[pi], meet[pj]), pos[pi] != pos[pj]))

# Number of meetings K (excluding Start)
K = Int("K")
opt.add(K == Sum([If(meet[p[0]], 1, 0) for p in people]))
opt.add(K >= 0, K <= N)

# Ensure positions are contiguous from 1..K (no gaps)
# For each k in 1..N, if k <= K then some person occupies position k
for k in range(1, N+1):
    occupants = [And(meet[p[0]], pos[p[0]] == k) for p in people]
    opt.add(Implies(k <= K, Or(occupants) if occupants else False))

# Adjacency travel constraints between consecutive positions
# If q is immediately after p (pos[q] == pos[p]+1), ensure travel feasibility
locations = {name: loc for (name, loc, _, _) in all_nodes}
names = [n for (n, _, _, _) in all_nodes]
for i in range(len(names)):
    for j in range(len(names)):
        if i == j:
            continue
        pi = names[i]
        pj = names[j]
        if (locations[pi], locations[pj]) not in TT:
            continue
        opt.add(Implies(And(meet[pi], meet[pj], pos[pj] == pos[pi] + 1),
                        end[pi] + tt(locations[pi], locations[pj]) <= start[pj]))

# Objective 1: maximize number of meetings (excluding Start)
opt.maximize(K)

# Objective 2: maximize total meeting time (excluding Start)
opt.maximize(Sum([dur[p[0]] for p in people]))

# Solve
if opt.check() != 1:
    # Infeasible (should not happen with given data)
    result = {"itinerary": []}
    print(json.dumps(result))
else:
    m = opt.model()

    # Build itinerary from met people sorted by start time
    itinerary = []
    for name, loc, (a_start, a_end), min_dur in people:
        if is_true(m[meet[name]]):
            st = m[start[name]].as_long()
            en = m[end[name]].as_long()
            itinerary.append({
                "action": "meet",
                "location": loc,
                "person": name,
                "start_time": minutes_to_str(st),
                "end_time": minutes_to_str(en),
            })

    # Sort by actual start time
    itinerary.sort(key=lambda x: (int(x["start_time"].split(":")[0]) * 60 + int(x["start_time"].split(":")[1])))

    print(json.dumps({"itinerary": itinerary}))