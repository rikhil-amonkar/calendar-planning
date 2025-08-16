import json
from z3 import Optimize, Int

def minutes_to_time(t):
    # Convert minutes since midnight to a string in HH:MM 24-hour format.
    hours = t // 60
    minutes = t % 60
    return f"{hours:02d}:{minutes:02d}"

# Create an optimizer instance (which supports optimization objectives)
opt = Optimize()

# Decision variables (times in minutes from midnight)
# dep: time you leave Russian Hill to travel
# daniel_start and daniel_end: start and end of meeting with Daniel at Richmond District
dep = Int("dep")
daniel_start = Int("daniel_start")
daniel_end = Int("daniel_end")

# Constants (in minutes since midnight)
start_time_RussianHill = 9 * 60           # 9:00 AM -> 540
travel_RH_to_Richmond = 14                # from Russian Hill to Richmond District
available_start_Daniel = 19 * 60          # 19:00 -> 1140 (Daniel arrives at Richmond District)
available_end_Daniel = 20 * 60 + 15         # 20:15 -> 1215 (Daniel leaves)
min_meeting_duration = 75                 # Must meet Daniel for at least 75 minutes

# Constraints:
# 1. You start your day at Russian Hill at 9:00.
opt.add(dep >= start_time_RussianHill)

# 2. You must finish your travel from Russian Hill to Richmond District before you start meeting Daniel.
opt.add(dep + travel_RH_to_Richmond <= daniel_start)

# 3. Daniel is available from 19:00 to 20:15.
opt.add(daniel_start >= available_start_Daniel)
opt.add(daniel_end <= available_end_Daniel)

# 4. You want to meet Daniel for at least 75 minutes.
opt.add(daniel_end - daniel_start >= min_meeting_duration)

# Optimization objective:
# Ideally, we want to maximize our available time to meet other friends on Russian Hill.
# In order to do so, we want to leave as late as possible (subject to still catching Daniel on time).
# Note: The Daniel meeting duration is fixed by his availability.
opt.maximize(dep)

# Solve the scheduling problem.
if opt.check() == 'sat':
    m = opt.model()
    dep_val = m[dep].as_long()           # departure from Russian Hill (in minutes since midnight)
    ds_val = m[daniel_start].as_long()     # meeting start time with Daniel
    de_val = m[daniel_end].as_long()       # meeting end time with Daniel

    # For this problem, the optimal solution will be to leave Russian Hill at the latest possible time:
    # dep + 14 <= 1140  -> dep <= 1126, so the solver should choose dep = 1126.
    # Then you arrive exactly at 19:00 (1140), and meeting Daniel until 20:15 (1215) gives a 75 minute meeting.
    
    itinerary = [
        {
            "action": "meet",
            "person": "Daniel",
            "start_time": minutes_to_time(ds_val),
            "end_time": minutes_to_time(de_val)
        }
    ]

    # Output the itinerary as a JSON-formatted dictionary.
    print(json.dumps({"itinerary": itinerary}))
else:
    print("No solution found")