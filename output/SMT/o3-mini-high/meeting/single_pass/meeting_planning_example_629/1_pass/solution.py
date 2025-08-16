from z3 import Int, Solver, sat
import json

# Helper function to convert minutes since midnight to "HH:MM" 24-hour format.
def minutes_to_HHMM(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

# Create the Z3 solver
s = Solver()

# Define meeting start time variables (in minutes after midnight)
Margaret_start = Int('Margaret_start')
Matthew_start  = Int('Matthew_start')
Kimberly_start = Int('Kimberly_start')
Nancy_start    = Int('Nancy_start')
Kenneth_start  = Int('Kenneth_start')
Helen_start    = Int('Helen_start')
Rebecca_start  = Int('Rebecca_start')

# Meeting durations (in minutes)
duration_Margaret = 90
duration_Matthew  = 90
duration_Kimberly = 120
duration_Nancy    = 15
duration_Kenneth  = 60
duration_Helen    = 60
duration_Rebecca  = 60

# Available time windows (in minutes after midnight)
# Margaret is at Chinatown from 9:15 (555) to 18:45 (1125)
s.add(Margaret_start >= 555)
s.add(Margaret_start + duration_Margaret <= 1125)

# Matthew is at Presidio from 11:00 (660) to 21:00 (1260)
s.add(Matthew_start >= 660)
s.add(Matthew_start + duration_Matthew <= 1260)

# Kimberly is at Golden Gate Park from 13:00 (780) to 16:30 (990)
s.add(Kimberly_start >= 780)
s.add(Kimberly_start + duration_Kimberly <= 990)

# Nancy is at Pacific Heights from 14:15 (855) to 17:00 (1020)
s.add(Nancy_start >= 855)
s.add(Nancy_start + duration_Nancy <= 1020)

# Kenneth is at Bayview from 14:30 (870) to 18:00 (1080)
s.add(Kenneth_start >= 870)
s.add(Kenneth_start + duration_Kenneth <= 1080)

# Helen is at Richmond District from 19:45 (1185) to 22:00 (1320)
s.add(Helen_start >= 1185)
s.add(Helen_start + duration_Helen <= 1320)

# Rebecca is at Fisherman's Wharf from 21:15 (1275) to 22:15 (1335)
s.add(Rebecca_start >= 1275)
s.add(Rebecca_start + duration_Rebecca <= 1335)

# We start at Russian Hill at 9:00 (540 minutes)
start_RussianHill = 540

# We choose the following route order based on travel times between locations:
# Russian Hill -> Chinatown -> Presidio -> Golden Gate Park -> Pacific Heights -> Bayview -> Richmond District -> Fisherman's Wharf

# Travel constraints:
# 1. Russian Hill to Chinatown: 9 minutes (for Margaret)
s.add(Margaret_start >= start_RussianHill + 9)

# 2. Chinatown to Presidio: 19 minutes (for Matthew)
s.add(Matthew_start >= Margaret_start + duration_Margaret + 19)

# 3. Presidio to Golden Gate Park: 12 minutes (for Kimberly)
s.add(Kimberly_start >= Matthew_start + duration_Matthew + 12)

# 4. Golden Gate Park to Pacific Heights: 15 minutes (for Nancy)
s.add(Nancy_start >= Kimberly_start + duration_Kimberly + 15)

# 5. Pacific Heights to Bayview: 22 minutes (for Kenneth)
s.add(Kenneth_start >= Nancy_start + duration_Nancy + 22)

# 6. Bayview to Richmond District: 25 minutes (for Helen)
s.add(Helen_start >= Kenneth_start + duration_Kenneth + 25)

# 7. Richmond District to Fisherman's Wharf: 18 minutes (for Rebecca)
s.add(Rebecca_start >= Helen_start + duration_Helen + 18)

# Attempt to solve the constraints
if s.check() == sat:
    m = s.model()
    itinerary = []
    # Define the meeting order with corresponding Z3 variables and required durations.
    meetings = [
        ("Margaret", Margaret_start, duration_Margaret),
        ("Matthew",  Matthew_start,  duration_Matthew),
        ("Kimberly", Kimberly_start, duration_Kimberly),
        ("Nancy",    Nancy_start,    duration_Nancy),
        ("Kenneth",  Kenneth_start,  duration_Kenneth),
        ("Helen",    Helen_start,    duration_Helen),
        ("Rebecca",  Rebecca_start,  duration_Rebecca)
    ]
    # Build the itinerary list with computed start and end times in HH:MM format.
    for person, start_var, dur in meetings:
        start_time = m[start_var].as_long()
        end_time = start_time + dur
        itinerary.append({
            "action": "meet",
            "person": person,
            "start_time": minutes_to_HHMM(start_time),
            "end_time": minutes_to_HHMM(end_time)
        })
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    print("No solution found")