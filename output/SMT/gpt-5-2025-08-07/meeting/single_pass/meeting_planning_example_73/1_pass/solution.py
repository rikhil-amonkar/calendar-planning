# Z3-based scheduler for meeting Barbara in San Francisco
# Constraints:
# - Arrive at Russian Hill at 09:00 (540 minutes)
# - Travel time Russian Hill -> Pacific Heights: 7 minutes
# - Barbara at Pacific Heights from 07:15 (435) to 22:00 (1320)
# - Meet Barbara for at least 60 minutes
# Objective:
# - Maximize total meeting time (only Barbara specified)

from z3 import Optimize, Int, And
import json

def minutes(h, m):
    return h*60 + m

def to_hhmm(t):
    h = t // 60
    m = t % 60
    return f"{h:02d}:{m:02d}"

# Constants
ARRIVAL_RUSSIAN_HILL = minutes(9, 0)        # 09:00
TRAVEL_RH_TO_PH = 7                          # minutes
BARBARA_START = minutes(7, 15)               # 07:15
BARBARA_END = minutes(22, 0)                 # 22:00
MIN_MEET = 60                                # minutes

# Z3 model
opt = Optimize()

s_b = Int('s_b')  # meeting start (minutes since midnight)
e_b = Int('e_b')  # meeting end   (minutes since midnight)

constraints = [
    s_b >= BARBARA_START,
    e_b <= BARBARA_END,
    e_b > s_b,
    e_b - s_b >= MIN_MEET,
    # Must travel from Russian Hill at 09:00 to Pacific Heights (7 minutes)
    s_b >= ARRIVAL_RUSSIAN_HILL + TRAVEL_RH_TO_PH,
    # Keep within bounds of day
    s_b >= 0,
    e_b <= 24*60
]

opt.add(And(*constraints))

# Objective: maximize meeting duration with Barbara
opt.maximize(e_b - s_b)

if opt.check().r == 1:
    m = opt.model()
    sb = m[s_b].as_long()
    eb = m[e_b].as_long()
    result = {
        "itinerary": [
            {
                "action": "meet",
                "person": "Barbara",
                "start_time": to_hhmm(sb),
                "end_time": to_hhmm(eb)
            }
        ]
    }
else:
    # Fallback (should not happen with given constraints)
    # Meet as soon as possible for the minimum duration, clipped to availability
    sb = max(BARBARA_START, ARRIVAL_RUSSIAN_HILL + TRAVEL_RH_TO_PH)
    eb = min(BARBARA_END, sb + MIN_MEET)
    result = {
        "itinerary": [
            {
                "action": "meet",
                "person": "Barbara",
                "start_time": to_hhmm(sb),
                "end_time": to_hhmm(eb)
            }
        ]
    }

print(json.dumps(result))