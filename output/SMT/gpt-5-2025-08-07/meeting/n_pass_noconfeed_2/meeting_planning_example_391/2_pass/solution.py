from z3 import *
import json

def minutes_to_str(m):
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

# Locations
SUNSET = "Sunset District"
ALAMO = "Alamo Square"
RUSSIAN = "Russian Hill"
PRESIDIO = "Presidio"
FINANCIAL = "Financial District"

# Travel times (minutes)
travel = {
    (SUNSET, ALAMO): 17,
    (SUNSET, RUSSIAN): 24,
    (SUNSET, PRESIDIO): 16,
    (SUNSET, FINANCIAL): 30,
    (ALAMO, SUNSET): 16,
    (ALAMO, RUSSIAN): 13,
    (ALAMO, PRESIDIO): 18,
    (ALAMO, FINANCIAL): 17,
    (RUSSIAN, SUNSET): 23,
    (RUSSIAN, ALAMO): 15,
    (RUSSIAN, PRESIDIO): 14,
    (RUSSIAN, FINANCIAL): 11,
    (PRESIDIO, SUNSET): 15,
    (PRESIDIO, ALAMO): 18,
    (PRESIDIO, RUSSIAN): 14,
    (PRESIDIO, FINANCIAL): 23,
    (FINANCIAL, SUNSET): 31,
    (FINANCIAL, ALAMO): 17,
    (FINANCIAL, RUSSIAN): 10,
    (FINANCIAL, PRESIDIO): 22,
}
# Add zero-time self-travel to avoid KeyError when same location/person pair is considered
for loc in [SUNSET, ALAMO, RUSSIAN, PRESIDIO, FINANCIAL]:
    travel[(loc, loc)] = 0

# People and constraints
people = [
    {"id": 1, "name": "Kevin", "location": ALAMO, "avail_start": 8*60+15, "avail_end": 21*60+30, "min_duration": 75},
    {"id": 2, "name": "Kimberly", "location": RUSSIAN, "avail_start": 8*60+45, "avail_end": 12*60+30, "min_duration": 30},
    {"id": 3, "name": "Joseph", "location": PRESIDIO, "avail_start": 18*60+30, "avail_end": 19*60+15, "min_duration": 45},
    {"id": 4, "name": "Thomas", "location": FINANCIAL, "avail_start": 19*60, "avail_end": 21*60+45, "min_duration": 45},
]
id_to_person = {p["id"]: p for p in people}

# Start time at Sunset District
day_start = 9*60  # 9:00

# Number of possible meeting slots (at most number of people)
K = len(people)

opt = Optimize()

# Variables for each slot
slot_person = [Int(f"slot_person_{i}") for i in range(K)]  # 0 means empty, else person id 1..4
slot_start = [Int(f"slot_start_{i}") for i in range(K)]
slot_end = [Int(f"slot_end_{i}") for i in range(K)]

# Domains
for i in range(K):
    opt.add(slot_person[i] >= 0, slot_person[i] <= len(people))
    opt.add(slot_start[i] >= 0, slot_end[i] >= 0)

# Contiguity: once a slot is empty, all following slots must be empty
for i in range(1, K):
    opt.add(Implies(slot_person[i-1] == 0, slot_person[i] == 0))

# Meeting constraints per slot
for i in range(K):
    # If empty slot, start and end are 0
    opt.add(Implies(slot_person[i] == 0, And(slot_start[i] == 0, slot_end[i] == 0)))

    # If assigned to a person, enforce availability and duration
    for pid in range(1, len(people)+1):
        p = id_to_person[pid]
        opt.add(Implies(
            slot_person[i] == pid,
            And(
                slot_start[i] >= p["avail_start"],
                slot_end[i] == slot_start[i] + p["min_duration"],
                slot_end[i] <= p["avail_end"]
            )
        ))

# No duplicate person across slots (allowing zeros)
for i in range(K):
    for j in range(i+1, K):
        opt.add(Or(slot_person[i] == 0, slot_person[j] == 0, slot_person[i] != slot_person[j]))

# Travel constraints between consecutive non-empty slots
for i in range(1, K):
    for prev_pid in range(1, len(people)+1):
        for curr_pid in range(1, len(people)+1):
            loc_prev = id_to_person[prev_pid]["location"]
            loc_curr = id_to_person[curr_pid]["location"]
            t = travel[(loc_prev, loc_curr)]
            opt.add(Implies(
                And(slot_person[i-1] == prev_pid, slot_person[i] == curr_pid),
                slot_start[i] >= slot_end[i-1] + t
            ))

# First slot must be reachable from Sunset District at 9:00
for pid in range(1, len(people)+1):
    loc = id_to_person[pid]["location"]
    t0 = travel[(SUNSET, loc)]
    opt.add(Implies(slot_person[0] == pid, slot_start[0] >= day_start + t0))

# Objective: maximize number of meetings (non-empty slots)
num_meetings = Sum([If(slot_person[i] == 0, 0, 1) for i in range(K)])
h1 = opt.maximize(num_meetings)

# Secondary objective: minimize end time of last meeting
last_end = Int("last_end")
opt.add(last_end >= 0)
for i in range(K):
    opt.add(Implies(slot_person[i] != 0, last_end >= slot_end[i]))
h2 = opt.minimize(last_end)

res = opt.check()
itinerary = []

if res == sat:
    m = opt.model()
    for i in range(K):
        pid_val = m.eval(slot_person[i]).as_long()
        if pid_val == 0:
            continue
        p = id_to_person[pid_val]
        s = m.eval(slot_start[i]).as_long()
        e = m.eval(slot_end[i]).as_long()
        itinerary.append({
            "action": "meet",
            "location": p["location"],
            "person": p["name"],
            "start_time": minutes_to_str(s),
            "end_time": minutes_to_str(e)
        })

output = {"itinerary": itinerary}
print(json.dumps(output, ensure_ascii=False))