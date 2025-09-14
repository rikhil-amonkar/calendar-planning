"SOLUTION:"

from z3 import *
import json

def format_time(mins_from_9am):
    # Convert minutes offset from 9:00 to H:MM 24-hour format (no leading zero for hour)
    total_minutes = 9 * 60 + mins_from_9am
    h = total_minutes // 60
    m = total_minutes % 60
    return f"{h}:{m:02d}"

# Location codes
NONE = 0
US = 1           # Union Square
PRESIDIO = 2     # Presidio

# Travel times (in minutes)
# Bayview to Union Square: 17
# Bayview to Presidio: 31
# Union Square to Bayview: 15 (unused)
# Union Square to Presidio: 24
# Presidio to Bayview: 31 (unused)
# Presidio to Union Square: 22
def travel_from_start(L):
    # From Bayview at 9:00 to first location
    return If(L == US, IntVal(17), IntVal(31))  # L is either US or PRESIDIO

def travel_between(L_from, L_to):
    return If(And(L_from == US, L_to == PRESIDIO), IntVal(24),
           If(And(L_from == PRESIDIO, L_to == US), IntVal(22), IntVal(0)))

# Availability windows relative to 9:00 (in minutes)
# Richard @ Union Square: 8:45 to 13:00 => [-15, 240]
# Charles @ Presidio:     9:45 to 13:00 => [ 45, 240]
def avail_start(L):
    return If(L == US, IntVal(-15),
           If(L == PRESIDIO, IntVal(45), IntVal(0)))

def avail_end(L):
    # Both end at 13:00 -> 240 minutes after 9:00
    return IntVal(240)

# Create optimizer
opt = Optimize()
opt.set(priority='lex')

# Decision variables
L1 = Int('L1')   # First meeting location: US or PRESIDIO
L2 = Int('L2')   # Second meeting location: NONE, US, or PRESIDIO (and if not NONE, must differ from L1)

start1 = Int('start1')
dur1 = Int('dur1')
end1 = Int('end1')

start2 = Int('start2')
dur2 = Int('dur2')
end2 = Int('end2')

# Domains for locations
opt.add(Or(L1 == US, L1 == PRESIDIO))
opt.add(Or(L2 == NONE, L2 == US, L2 == PRESIDIO))
# If there is a second meeting, it must be at a different location
opt.add(Implies(L2 != NONE, L2 != L1))

# First segment timing constraints
opt.add(start1 >= 0)
opt.add(dur1 >= 0)
opt.add(end1 == start1 + dur1)
opt.add(start1 >= travel_from_start(L1))           # can't start before arriving
opt.add(start1 >= avail_start(L1))                 # can't start before availability
opt.add(end1 <= avail_end(L1))                     # must finish within availability end
opt.add(end1 <= 240)                               # within day horizon

# Second segment timing constraints (guarded by L2 != NONE)
t12 = travel_between(L1, L2)
opt.add(start2 >= 0)
opt.add(dur2 >= 0)
opt.add(end2 == start2 + dur2)

opt.add(Implies(L2 != NONE, start2 >= end1 + t12))
opt.add(Implies(L2 != NONE, start2 >= avail_start(L2)))
opt.add(Implies(L2 != NONE, end2 <= avail_end(L2)))
opt.add(Implies(L2 != NONE, end2 <= 240))

# If no second segment, force zero times for cleanliness
opt.add(Implies(L2 == NONE, And(start2 == 0, dur2 == 0, end2 == 0)))

# Meeting minutes per person
minutes_Richard = If(L1 == US, dur1, IntVal(0)) + If(L2 == US, dur2, IntVal(0))
minutes_Charles = If(L1 == PRESIDIO, dur1, IntVal(0)) + If(L2 == PRESIDIO, dur2, IntVal(0))

# Satisfaction indicators (1 if at least 120 minutes)
sat_R = If(minutes_Richard >= 120, IntVal(1), IntVal(0))
sat_C = If(minutes_Charles >= 120, IntVal(1), IntVal(0))

# Objectives:
# 1) Maximize number of satisfied friends
# 2) Maximize total meeting minutes
opt.maximize(sat_R + sat_C)
opt.maximize(minutes_Richard + minutes_Charles)

# Solve
if opt.check() != sat:
    # Should not happen with given data, but handle gracefully
    print(json.dumps({"itinerary": []}))
else:
    m = opt.model()

    # Extract values
    v_L1 = m[L1].as_long()
    v_L2 = m[L2].as_long()

    v_start1 = m[start1].as_long()
    v_end1 = m[end1].as_long()
    v_dur1 = m[dur1].as_long()

    v_start2 = m[start2].as_long()
    v_end2 = m[end2].as_long()
    v_dur2 = m[dur2].as_long()

    # Build itinerary
    itinerary = []

    def loc_name(code):
        return "Union Square" if code == US else ("Presidio" if code == PRESIDIO else "")

    def person_name(code):
        return "Richard" if code == US else ("Charles" if code == PRESIDIO else "")

    # Segment 1
    if v_dur1 > 0:
        itinerary.append({
            "action": "meet",
            "location": loc_name(v_L1),
            "person": person_name(v_L1),
            "start_time": format_time(v_start1),
            "end_time": format_time(v_end1)
        })

    # Segment 2
    if v_L2 != NONE and v_dur2 > 0:
        itinerary.append({
            "action": "meet",
            "location": loc_name(v_L2),
            "person": person_name(v_L2),
            "start_time": format_time(v_start2),
            "end_time": format_time(v_end2)
        })

    # Sort by start_time minutes (convert back temporarily)
    def to_minutes(tstr):
        h, m = tstr.split(':')
        return int(h) * 60 + int(m)

    itinerary.sort(key=lambda e: to_minutes(e["start_time"]))

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))