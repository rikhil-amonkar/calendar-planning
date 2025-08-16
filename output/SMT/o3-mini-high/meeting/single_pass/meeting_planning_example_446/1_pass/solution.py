from z3 import *
import json

# Helper function: Convert minutes (since midnight) to HH:MM string.
def minutes_to_HHMM(m):
    h = m // 60
    minute = m % 60
    return f"{h:02d}:{minute:02d}"

# Create Z3 integer variables for each meeting's start and end times.
# Times are represented as minutes from midnight.
margaret_start, margaret_end = Ints('margaret_start margaret_end')
robert_start, robert_end     = Ints('robert_start robert_end')
rebecca_start, rebecca_end   = Ints('rebecca_start rebecca_end')
kimberly_start, kimberly_end = Ints('kimberly_start kimberly_end')
kenneth_start, kenneth_end     = Ints('kenneth_start kenneth_end')

# Create the solver
s = Solver()

# Constants: start-of-day conditions (in minutes since midnight)
# You arrive at Richmond District at 9:00 AM = 540 minutes.
start_time = 540

# Friend availability windows (converted to minutes):
# Margaret (Bayview): 9:30 (570) to 13:30 (810), min meeting = 30 minutes.
s.add(margaret_start >= 570)      # available from 9:30
s.add(margaret_end <= 810)        # must finish by 13:30
s.add(margaret_end - margaret_start >= 30)
# For simplicity, we fix the meeting to the minimum required duration.
s.add(margaret_end == margaret_start + 30)

# Robert (Chinatown): 12:15 (735) to 20:15 (1215), min meeting = 15 minutes.
s.add(robert_start >= 735)        # available from 12:15
s.add(robert_end <= 1215)         # must finish by 20:15
s.add(robert_end - robert_start >= 15)
s.add(robert_end == robert_start + 15)

# Rebecca (Financial District): 13:15 (795) to 16:45 (1005), min meeting = 75 minutes.
s.add(rebecca_start >= 795)       # available from 13:15
s.add(rebecca_end <= 1005)        # must finish by 16:45
s.add(rebecca_end - rebecca_start >= 75)
s.add(rebecca_end == rebecca_start + 75)

# Kimberly (Marina District): 13:15 (795) to 16:45 (1005), min meeting = 15 minutes.
s.add(kimberly_start >= 795)      # available from 13:15
s.add(kimberly_end <= 1005)       # must finish by 16:45
s.add(kimberly_end - kimberly_start >= 15)
s.add(kimberly_end == kimberly_start + 15)

# Kenneth (Union Square): 19:30 (1170) to 21:15 (1275), min meeting = 75 minutes.
s.add(kenneth_start >= 1170)      # available from 19:30
s.add(kenneth_end <= 1275)        # must finish by 21:15
s.add(kenneth_end - kenneth_start >= 75)
s.add(kenneth_end == kenneth_start + 75)

# Travel times (in minutes) between districts, as given:
# You start at Richmond District at 9:00.
# For each leg, we add travel time constraints based on the chosen order:
#
# Proposed meeting order (and corresponding districts):
# 1. Margaret at Bayview
# 2. Robert at Chinatown
# 3. Rebecca at Financial District
# 4. Kimberly at Marina District
# 5. Kenneth at Union Square
#
# Constraint: You must leave the previous meeting room and travel to the next.
#
# From Richmond District to Bayview: travel time = 26 minutes.
s.add(margaret_start >= start_time + 26)

# From Bayview (Margaret) to Chinatown (Robert):  Bayview to Chinatown = 18 minutes.
s.add(robert_start >= margaret_end + 18)

# From Chinatown (Robert) to Financial District (Rebecca): Chinatown to Financial = 5 minutes.
s.add(rebecca_start >= robert_end + 5)

# From Financial District (Rebecca) to Marina District (Kimberly): Financial to Marina = 15 minutes.
s.add(kimberly_start >= rebecca_end + 15)

# From Marina District (Kimberly) to Union Square (Kenneth): Marina to Union Square = 16 minutes.
s.add(kenneth_start >= kimberly_end + 16)

# Check for a feasible solution.
if s.check() == sat:
    m = s.model()
    itinerary = []
    
    itinerary.append({
        "action": "meet",
        "person": "Margaret",
        "start_time": minutes_to_HHMM(m[margaret_start].as_long()),
        "end_time": minutes_to_HHMM(m[margaret_end].as_long())
    })
    itinerary.append({
        "action": "meet",
        "person": "Robert",
        "start_time": minutes_to_HHMM(m[robert_start].as_long()),
        "end_time": minutes_to_HHMM(m[robert_end].as_long())
    })
    itinerary.append({
        "action": "meet",
        "person": "Rebecca",
        "start_time": minutes_to_HHMM(m[rebecca_start].as_long()),
        "end_time": minutes_to_HHMM(m[rebecca_end].as_long())
    })
    itinerary.append({
        "action": "meet",
        "person": "Kimberly",
        "start_time": minutes_to_HHMM(m[kimberly_start].as_long()),
        "end_time": minutes_to_HHMM(m[kimberly_end].as_long())
    })
    itinerary.append({
        "action": "meet",
        "person": "Kenneth",
        "start_time": minutes_to_HHMM(m[kenneth_start].as_long()),
        "end_time": minutes_to_HHMM(m[kenneth_end].as_long())
    })

    # Create the final JSON output.
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))
else:
    print("No solution found.")