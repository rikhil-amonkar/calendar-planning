# Z3-based optimizer for meeting as many friends as possible given travel times and availability windows.
# It prints a JSON itinerary with the selected meetings and times.

from z3 import Optimize, Int, Bool, If, And, Or, Not, Sum, sat
import json

def minutes(h, m):
    return h * 60 + m

# Locations
Mission = "Mission District"
Castro = "The Castro"
NobHill = "Nob Hill"
Presidio = "Presidio"
Marina = "Marina District"
PacificHeights = "Pacific Heights"
GGPark = "Golden Gate Park"
Chinatown = "Chinatown"
Richmond = "Richmond District"

# Travel time matrix in minutes (directed, as provided)
T = {}
def set_t(a,b,t): T[(a,b)] = t

set_t(Mission, Castro, 7)
set_t(Mission, NobHill, 12)
set_t(Mission, Presidio, 25)
set_t(Mission, Marina, 19)
set_t(Mission, PacificHeights, 16)
set_t(Mission, GGPark, 17)
set_t(Mission, Chinatown, 16)
set_t(Mission, Richmond, 20)

set_t(Castro, Mission, 7)
set_t(Castro, NobHill, 16)
set_t(Castro, Presidio, 20)
set_t(Castro, Marina, 21)
set_t(Castro, PacificHeights, 16)
set_t(Castro, GGPark, 11)
set_t(Castro, Chinatown, 22)
set_t(Castro, Richmond, 16)

set_t(NobHill, Mission, 13)
set_t(NobHill, Castro, 17)
set_t(NobHill, Presidio, 17)
set_t(NobHill, Marina, 11)
set_t(NobHill, PacificHeights, 8)
set_t(NobHill, GGPark, 17)
set_t(NobHill, Chinatown, 6)
set_t(NobHill, Richmond, 14)

set_t(Presidio, Mission, 26)
set_t(Presidio, Castro, 21)
set_t(Presidio, NobHill, 18)
set_t(Presidio, Marina, 11)
set_t(Presidio, PacificHeights, 11)
set_t(Presidio, GGPark, 12)
set_t(Presidio, Chinatown, 21)
set_t(Presidio, Richmond, 7)

set_t(Marina, Mission, 20)
set_t(Marina, Castro, 22)
set_t(Marina, NobHill, 12)
set_t(Marina, Presidio, 10)
set_t(Marina, PacificHeights, 7)
set_t(Marina, GGPark, 18)
set_t(Marina, Chinatown, 15)
set_t(Marina, Richmond, 11)

set_t(PacificHeights, Mission, 15)
set_t(PacificHeights, Castro, 16)
set_t(PacificHeights, NobHill, 8)
set_t(PacificHeights, Presidio, 11)
set_t(PacificHeights, Marina, 6)
set_t(PacificHeights, GGPark, 15)
set_t(PacificHeights, Chinatown, 11)
set_t(PacificHeights, Richmond, 12)

set_t(GGPark, Mission, 17)
set_t(GGPark, Castro, 13)
set_t(GGPark, NobHill, 20)
set_t(GGPark, Presidio, 11)
set_t(GGPark, Marina, 16)
set_t(GGPark, PacificHeights, 16)
set_t(GGPark, Chinatown, 23)
set_t(GGPark, Richmond, 7)

set_t(Chinatown, Mission, 17)
set_t(Chinatown, Castro, 22)
set_t(Chinatown, NobHill, 9)
set_t(Chinatown, Presidio, 19)
set_t(Chinatown, Marina, 12)
set_t(Chinatown, PacificHeights, 10)
set_t(Chinatown, GGPark, 23)
set_t(Chinatown, Richmond, 20)

set_t(Richmond, Mission, 20)
set_t(Richmond, Castro, 16)
set_t(Richmond, NobHill, 17)
set_t(Richmond, Presidio, 7)
set_t(Richmond, Marina, 9)
set_t(Richmond, PacificHeights, 10)
set_t(Richmond, GGPark, 9)
set_t(Richmond, Chinatown, 20)

# Friends data: name -> (location, window_start, window_end, min_duration)
friends = {
    "Lisa":      (Castro,         minutes(19,15), minutes(21,15), 120),
    "Daniel":    (NobHill,        minutes(8,15),  minutes(11,0),   15),
    "Elizabeth": (Presidio,       minutes(21,15), minutes(22,15),  45),
    "Steven":    (Marina,         minutes(16,30), minutes(20,45),  90),
    "Timothy":   (PacificHeights, minutes(12,0),  minutes(18,0),   90),
    "Ashley":    (GGPark,         minutes(20,45), minutes(21,45),  60),
    "Kevin":     (Chinatown,      minutes(12,0),  minutes(19,0),   30),
    "Betty":     (Richmond,       minutes(13,15), minutes(15,45),  30),
}

start_loc = Mission
arrival_time = minutes(9,0)

# Z3 model
opt = Optimize()

start = {}
end = {}
meet = {}

for p, (loc, wstart, wend, mindur) in friends.items():
    start[p] = Int(f"start_{p}")
    end[p] = Int(f"end_{p}")
    meet[p] = Bool(f"meet_{p}")
    # bounds
    opt.add(start[p] >= 0, start[p] <= 24*60)
    opt.add(end[p] >= 0, end[p] <= 24*60)
    opt.add(end[p] >= start[p])

    # If meeting, respect window and duration
    opt.add(If(meet[p],
               And(start[p] >= wstart,
                   end[p] <= wend,
                   end[p] - start[p] >= mindur,
                   # also must be reachable at least from start location at 9:00
                   start[p] >= arrival_time + T[(start_loc, friends[p][0])]
               ),
               # If not meeting, we can set start=end=0 (or leave unconstrained; we choose to pin to 0 for clarity)
               And(start[p] == 0, end[p] == 0)
               ))

# Pairwise ordering with travel times: if both met, they cannot overlap and must allow for travel either way
people = list(friends.keys())
for i in range(len(people)):
    for j in range(i+1, len(people)):
        pi, pj = people[i], people[j]
        li, lj = friends[pi][0], friends[pj][0]
        tij = T[(li, lj)]
        tji = T[(lj, li)]
        opt.add(Or(Not(And(meet[pi], meet[pj])),
                   Or(start[pj] >= end[pi] + tij,
                      start[pi] >= end[pj] + tji)))

# Objective: maximize number of friends met
opt.maximize(Sum([If(meet[p], 1, 0) for p in people]))

# Optional tie-breakers: minimize total waiting/travel (not strictly needed)
# Here we do a mild secondary objective: minimize latest end time (to prefer earlier finish).
opt.minimize(Sum([end[p] for p in people]))

res = opt.check()
assert res == sat, "No feasible schedule found"

m = opt.model()

meetings = []
for p in people:
    if m.evaluate(meet[p], model_completion=True):
        st = m.evaluate(start[p]).as_long()
        en = m.evaluate(end[p]).as_long()
        meetings.append((st, en, p))

# Sort by start time
meetings.sort(key=lambda x: x[0])

def fmt(t):
    h = t // 60
    mi = t % 60
    return f"{h:02d}:{mi:02d}"

itinerary = []
for st, en, p in meetings:
    itinerary.append({
        "action": "meet",
        "person": p,
        "start_time": fmt(st),
        "end_time": fmt(en)
    })

print(json.dumps({"itinerary": itinerary}))