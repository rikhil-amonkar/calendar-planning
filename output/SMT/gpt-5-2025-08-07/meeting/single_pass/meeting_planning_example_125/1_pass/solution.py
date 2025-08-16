from z3 import Optimize, Int, And, Or, If
import json

def minutes(h, m):
    return h * 60 + m

def fmt_time(mins):
    h = mins // 60
    m = mins % 60
    return f"{h:02d}:{m:02d}"

# Travel times (minutes)
t_E_FD = 5
t_FD_E = 4
t_E_AS = 19
t_AS_E = 17
t_FD_AS = 17
t_AS_FD = 17

# Availability windows (minutes from midnight)
# Arrive Embarcadero at 09:00
arrive_E = minutes(9, 0)

# Stephanie at Financial District 08:15-11:30, min 90 minutes
S_avail_start = minutes(8, 15)
S_avail_end   = minutes(11, 30)
S_min_dur     = 90

# John at Alamo Square 10:15-20:45, min 30 minutes
J_avail_start = minutes(10, 15)
J_avail_end   = minutes(20, 45)
J_min_dur     = 30

opt = Optimize()
opt.set(priority='lex')

# Decision variables
s_start = Int('s_start')
s_end   = Int('s_end')
j_start = Int('j_start')
j_end   = Int('j_end')
meet_s  = Int('meet_s')  # 0/1
meet_j  = Int('meet_j')  # 0/1
order   = Int('order')   # 0 -> S then J, 1 -> J then S (only relevant if both == 1)
last_end = Int('last_end')

# Domains
opt.add(meet_s >= 0, meet_s <= 1, meet_j >= 0, meet_j <= 1)
opt.add(order >= 0, order <= 1)
opt.add(s_start >= 0, s_start <= 24*60, s_end >= 0, s_end <= 24*60)
opt.add(j_start >= 0, j_start <= 24*60, j_end >= 0, j_end <= 24*60)
opt.add(last_end >= 0, last_end <= 24*60)

# Meeting feasibility constraints (conditional)
opt.add(And(
    # Stephanie window and duration if meeting her
    If(meet_s == 1, And(s_start >= S_avail_start,
                        s_end   <= S_avail_end,
                        s_end - s_start >= S_min_dur), True),
    # John window and duration if meeting him
    If(meet_j == 1, And(j_start >= J_avail_start,
                        j_end   <= J_avail_end,
                        j_end - j_start >= J_min_dur), True)
))

# Travel/ordering constraints
# Only S
opt.add(If(And(meet_s == 1, meet_j == 0),
           s_start >= arrive_E + t_E_FD,
           True))

# Only J
opt.add(If(And(meet_s == 0, meet_j == 1),
           j_start >= arrive_E + t_E_AS,
           True))

# Both: order 0 (S then J)
opt.add(If(And(meet_s == 1, meet_j == 1, order == 0),
           And(
               s_start >= arrive_E + t_E_FD,
               j_start >= s_end + t_FD_AS,
               s_end <= j_start  # no overlap
           ),
           True))

# Both: order 1 (J then S)
opt.add(If(And(meet_s == 1, meet_j == 1, order == 1),
           And(
               j_start >= arrive_E + t_E_AS,
               s_start >= j_end + t_AS_FD,
               j_end <= s_start  # no overlap
           ),
           True))

# Track last_end to minimize end-of-day time as secondary objective
opt.add(last_end >= If(meet_s == 1, s_end, 0))
opt.add(last_end >= If(meet_j == 1, j_end, 0))

# Objectives:
# 1) Maximize number of friends met
obj1 = opt.maximize(meet_s + meet_j)
# 2) Minimize finish time (prefer earlier finish, minimal durations)
obj2 = opt.minimize(last_end)

if opt.check() != sat:
    print(json.dumps({"itinerary": []}))
else:
    m = opt.model()
    meetS = m[meet_s].as_long()
    meetJ = m[meet_j].as_long()

    itinerary = []

    if meetS == 1:
        s_start_v = m[s_start].as_long()
        s_end_v = m[s_end].as_long()
        itinerary.append({
            "action": "meet",
            "person": "Stephanie",
            "start_time": fmt_time(s_start_v),
            "end_time": fmt_time(s_end_v)
        })

    if meetJ == 1:
        j_start_v = m[j_start].as_long()
        j_end_v = m[j_end].as_long()
        itinerary.append({
            "action": "meet",
            "person": "John",
            "start_time": fmt_time(j_start_v),
            "end_time": fmt_time(j_end_v)
        })

    # Sort by start time
    itinerary.sort(key=lambda x: x["start_time"])
    print(json.dumps({"itinerary": itinerary}))