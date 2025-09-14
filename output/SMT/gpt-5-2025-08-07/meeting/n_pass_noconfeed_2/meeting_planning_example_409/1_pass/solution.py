import json
from z3 import *

# Define locations
locations = [
    "Fisherman's Wharf",
    "Bayview",
    "Golden Gate Park",
    "Nob Hill",
    "Marina District",
    "Embarcadero"
]
loc_index = {name: i for i, name in enumerate(locations)}

# Travel times (minutes)
T = {name: {} for name in locations}
def set_t(a, b, m):
    T[a][b] = m

# Fill travel matrix from the provided data
set_t("Fisherman's Wharf", "Bayview", 26)
set_t("Fisherman's Wharf", "Golden Gate Park", 25)
set_t("Fisherman's Wharf", "Nob Hill", 11)
set_t("Fisherman's Wharf", "Marina District", 9)
set_t("Fisherman's Wharf", "Embarcadero", 8)

set_t("Bayview", "Fisherman's Wharf", 25)
set_t("Bayview", "Golden Gate Park", 22)
set_t("Bayview", "Nob Hill", 20)
set_t("Bayview", "Marina District", 25)
set_t("Bayview", "Embarcadero", 19)

set_t("Golden Gate Park", "Fisherman's Wharf", 24)
set_t("Golden Gate Park", "Bayview", 23)
set_t("Golden Gate Park", "Nob Hill", 20)
set_t("Golden Gate Park", "Marina District", 16)
set_t("Golden Gate Park", "Embarcadero", 25)

set_t("Nob Hill", "Fisherman's Wharf", 11)
set_t("Nob Hill", "Bayview", 19)
set_t("Nob Hill", "Golden Gate Park", 17)
set_t("Nob Hill", "Marina District", 11)
set_t("Nob Hill", "Embarcadero", 9)

set_t("Marina District", "Fisherman's Wharf", 10)
set_t("Marina District", "Bayview", 27)
set_t("Marina District", "Golden Gate Park", 18)
set_t("Marina District", "Nob Hill", 12)
set_t("Marina District", "Embarcadero", 14)

set_t("Embarcadero", "Fisherman's Wharf", 6)
set_t("Embarcadero", "Bayview", 21)
set_t("Embarcadero", "Golden Gate Park", 25)
set_t("Embarcadero", "Nob Hill", 10)
set_t("Embarcadero", "Marina District", 12)

# Add zero travel for same-location moves
for a in locations:
    T[a][a] = 0

# Friends and constraints
# Times are minutes from midnight
def hm(h, m): return h*60 + m

friends = [
    {
        "name": "Thomas",
        "location": "Bayview",
        "loc_idx": loc_index["Bayview"],
        "avail_start": hm(15, 30),
        "avail_end": hm(18, 30),
        "min_meet": 120
    },
    {
        "name": "Stephanie",
        "location": "Golden Gate Park",
        "loc_idx": loc_index["Golden Gate Park"],
        "avail_start": hm(18, 30),
        "avail_end": hm(21, 45),
        "min_meet": 30
    },
    {
        "name": "Laura",
        "location": "Nob Hill",
        "loc_idx": loc_index["Nob Hill"],
        "avail_start": hm(8, 45),
        "avail_end": hm(16, 15),
        "min_meet": 30
    },
    {
        "name": "Betty",
        "location": "Marina District",
        "loc_idx": loc_index["Marina District"],
        "avail_start": hm(18, 45),
        "avail_end": hm(21, 45),
        "min_meet": 45
    },
    {
        "name": "Patricia",
        "location": "Embarcadero",
        "loc_idx": loc_index["Embarcadero"],
        "avail_start": hm(17, 30),
        "avail_end": hm(22, 0),
        "min_meet": 45
    }
]

N = len(friends)
K = N  # maximum number of meeting slots
START_LOC = "Fisherman's Wharf"
ARRIVAL_TIME = hm(9, 0)

# Precompute travel from start to each friend's location
start_to_friend = [T[START_LOC][friends[i]["location"]] for i in range(N)]

# Precompute inter-friend travel matrix by indices
friend_to_friend = [[0]*N for _ in range(N)]
for i in range(N):
    for j in range(N):
        li = friends[i]["location"]
        lj = friends[j]["location"]
        friend_to_friend[i][j] = T[li][lj]

# Z3 model
opt = Optimize()
opt.set(priority='lex')

# Variables per slot
slotUsed = [Bool(f"slotUsed_{s}") for s in range(K)]
slotFriend = [Int(f"slotFriend_{s}") for s in range(K)]
start_time = [Int(f"start_{s}") for s in range(K)]
end_time = [Int(f"end_{s}") for s in range(K)]

# Bounds and domain
for s in range(K):
    # time bounds
    opt.add(start_time[s] >= 0, start_time[s] <= 24*60)
    opt.add(end_time[s] >= 0, end_time[s] <= 24*60)
    # friend domain control
    opt.add(Implies(slotUsed[s], And(slotFriend[s] >= 0, slotFriend[s] < N)))
    opt.add(Implies(Not(slotUsed[s]), slotFriend[s] == -1))
    # meeting duration non-negative when used
    opt.add(Implies(slotUsed[s], end_time[s] >= start_time[s]))

# Used slots are a prefix (no gaps)
for s in range(1, K):
    opt.add(Implies(slotUsed[s], slotUsed[s-1]))

# Distinctness of friends across used slots
for s in range(K):
    for t in range(s+1, K):
        opt.add(Implies(And(slotUsed[s], slotUsed[t]), slotFriend[s] != slotFriend[t]))

# Meeting window and min duration constraints per slot based on selected friend
for s in range(K):
    for i in range(N):
        fs = friends[i]
        opt.add(
            Implies(
                And(slotUsed[s], slotFriend[s] == i),
                And(
                    start_time[s] >= fs["avail_start"],
                    end_time[s] <= fs["avail_end"],
                    end_time[s] - start_time[s] >= fs["min_meet"]
                )
            )
        )

# Travel constraints: from start to first used slot
if K > 0:
    s = 0
    for i in range(N):
        opt.add(
            Implies(
                And(slotUsed[s], slotFriend[s] == i),
                start_time[s] >= ARRIVAL_TIME + start_to_friend[i]
            )
        )

# Travel constraints between consecutive used slots
for s in range(1, K):
    for i in range(N):
        for j in range(N):
            opt.add(
                Implies(
                    And(slotUsed[s-1], slotFriend[s-1] == i, slotUsed[s], slotFriend[s] == j),
                    start_time[s] >= end_time[s-1] + friend_to_friend[i][j]
                )
            )

# Derive which friends are met
friendMet = [Bool(f"friendMet_{i}") for i in range(N)]
for i in range(N):
    occurrences = []
    for s in range(K):
        occurrences.append(And(slotUsed[s], slotFriend[s] == i))
    opt.add(friendMet[i] == Or(occurrences) if occurrences else False)

# Objectives: maximize number of friends met, then maximize total meeting time
totalMet = Sum([If(friendMet[i], 1, 0) for i in range(N)])
totalMinutes = Sum([If(slotUsed[s], end_time[s] - start_time[s], 0) for s in range(K)])
opt.maximize(totalMet)
opt.maximize(totalMinutes)

# Solve
if opt.check() != sat:
    # If unsat, output empty itinerary
    result = {"itinerary": []}
    print(json.dumps(result))
    exit(0)

model = opt.model()

# Build itinerary in order of slots
def fmt_time(m):
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

itinerary = []
for s in range(K):
    if is_true(model.evaluate(slotUsed[s])):
        fi = model.evaluate(slotFriend[s]).as_long()
        st = model.evaluate(start_time[s]).as_long()
        en = model.evaluate(end_time[s]).as_long()
        entry = {
            "action": "meet",
            "location": friends[fi]["location"],
            "person": friends[fi]["name"],
            "start_time": fmt_time(st),
            "end_time": fmt_time(en)
        }
        itinerary.append(entry)

print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))