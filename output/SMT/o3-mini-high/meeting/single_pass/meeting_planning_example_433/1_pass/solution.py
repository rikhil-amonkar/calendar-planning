from z3 import Solver, Int, sat
import json

def minutes_to_time(m):
    hrs = m // 60
    mins = m % 60
    return f"{hrs:02d}:{mins:02d}"

# Create Z3 integer variables representing the start times (in minutes from midnight)
jeffrey_start   = Int('jeffrey_start')
deborah_start   = Int('deborah_start')
margaret_start  = Int('margaret_start')
ronald_start    = Int('ronald_start')
emily_start     = Int('emily_start')

# Meeting durations (in minutes)
JEFFREY_DURATION  = 120  # Jeffrey at Golden Gate Park, from 11:15 (675) to 14:30 (870)
DEBORAH_DURATION  = 90   # Deborah at The Castro, from 13:45 (825) to 21:15 (1275)
MARGARET_DURATION = 75   # Margaret at Financial District, from 16:30 (990) to 20:15 (1215)
RONALD_DURATION   = 45   # Ronald at North Beach, from 18:30 (1110) to 19:30 (1170)
EMILY_DURATION    = 15   # Emily at Richmond District, from 19:00 (1140) to 21:00 (1260)

# Define the availability windows in minutes from midnight:
# 9:00 AM is 540.
# Jeffrey: available from 11:15 (675) to 14:30 (870)
# Deborah: available from 13:45 (825) to 21:15 (1275)
# Margaret: available from 16:30 (990) to 20:15 (1215)
# Ronald: available from 18:30 (1110) to 19:30 (1170)
# Emily: available from 19:00 (1140) to 21:00 (1260)

s = Solver()

# Each meeting must start no earlier than the friend’s available start and end (start+duration) no later than the available end.
s.add(jeffrey_start >= 675, jeffrey_start + JEFFREY_DURATION <= 870)
s.add(deborah_start >= 825, deborah_start + DEBORAH_DURATION <= 1275)
s.add(margaret_start >= 990, margaret_start + MARGARET_DURATION <= 1215)
s.add(ronald_start >= 1110, ronald_start + RONALD_DURATION <= 1170)
s.add(emily_start  >= 1140, emily_start  + EMILY_DURATION  <= 1260)

# Travel Constraints:
# You start at Nob Hill at 9:00 (540 minutes)
# Travel times between neighborhoods (in minutes):
# Nob Hill -> Golden Gate Park (Jeffrey): 17 minutes
s.add(jeffrey_start >= 540 + 17)

# Jeffrey (Golden Gate Park) -> Deborah (The Castro):
# Travel time from Golden Gate Park to The Castro: 13 minutes.
s.add(deborah_start >= jeffrey_start + JEFFREY_DURATION + 13)

# Deborah (The Castro) -> Margaret (Financial District):
# Travel time from The Castro to Financial District: 20 minutes.
s.add(margaret_start >= deborah_start + DEBORAH_DURATION + 20)

# Margaret (Financial District) -> Ronald (North Beach):
# Travel time from Financial District to North Beach: 7 minutes.
s.add(ronald_start >= margaret_start + MARGARET_DURATION + 7)

# Ronald (North Beach) -> Emily (Richmond District):
# Travel time from North Beach to Richmond District: 18 minutes.
s.add(emily_start >= ronald_start + RONALD_DURATION + 18)

# Try to solve the constraints.
if s.check() == sat:
    m = s.model()
    # Get the start times as integers.
    jeffrey_t = m[jeffrey_start].as_long()
    deborah_t = m[deborah_start].as_long()
    margaret_t = m[margaret_start].as_long()
    ronald_t   = m[ronald_start].as_long()
    emily_t    = m[emily_start].as_long()
    
    itinerary = [
        {
            "action": "meet", 
            "person": "Jeffrey", 
            "start_time": minutes_to_time(jeffrey_t),
            "end_time": minutes_to_time(jeffrey_t + JEFFREY_DURATION)
        },
        {
            "action": "meet", 
            "person": "Deborah", 
            "start_time": minutes_to_time(deborah_t),
            "end_time": minutes_to_time(deborah_t + DEBORAH_DURATION)
        },
        {
            "action": "meet", 
            "person": "Margaret", 
            "start_time": minutes_to_time(margaret_t),
            "end_time": minutes_to_time(margaret_t + MARGARET_DURATION)
        },
        {
            "action": "meet", 
            "person": "Ronald", 
            "start_time": minutes_to_time(ronald_t),
            "end_time": minutes_to_time(ronald_t + RONALD_DURATION)
        },
        {
            "action": "meet", 
            "person": "Emily", 
            "start_time": minutes_to_time(emily_t),
            "end_time": minutes_to_time(emily_t + EMILY_DURATION)
        }
    ]
    
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))
else:
    print("No solution found")