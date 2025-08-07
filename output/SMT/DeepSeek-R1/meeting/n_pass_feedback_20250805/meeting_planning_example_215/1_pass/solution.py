from z3 import *

def min_to_time(total_minutes):
    h = 9 + total_minutes // 60
    m = total_minutes % 60
    return f"{h:02d}:{m:02d}"

# Create variables
T0 = Int('T0')
S1 = Int('S1')
S2 = Int('S2')
S3 = Int('S3')

s = Solver()

# Fixed durations in minutes
D1 = 30
D2 = 30
D3 = 120

# Time windows in minutes from 9:00 AM
jason_start = 7 * 60        # 16:00 (4:00 PM) -> 420 minutes from 9:00 AM
jason_end = 7 * 60 + 45     # 16:45 (4:45 PM) -> 465 minutes
jessica_start = 7 * 60 + 45 # 16:45 (4:45 PM) -> 465 minutes
jessica_end = 10 * 60       # 19:00 (7:00 PM) -> 600 minutes
sandra_start = 9 * 60 + 30  # 18:30 (6:30 PM) -> 570 minutes
sandra_end = 12 * 60 + 45   # 21:45 (9:45 PM) -> 765 minutes

# Constraints
s.add(T0 >= 0)  # Departure from Bayview at or after 9:00 AM

# Travel from Bayview to Fisherman's Wharf: 25 minutes
s.add(S1 >= T0 + 25)  # Start meeting with Jason after arrival
s.add(S1 >= jason_start)
s.add(S1 + D1 <= jason_end)  # Jason's meeting must end by 16:45

# Travel from Fisherman's Wharf to Embarcadero: 8 minutes
arrival_embarcadero = S1 + D1 + 8
s.add(S2 >= arrival_embarcadero)  # Start meeting with Jessica after arrival
s.add(S2 >= jessica_start)
s.add(S2 + D2 <= jessica_end)  # Jessica's meeting must end by 19:00

# Travel from Embarcadero to Richmond District: 21 minutes
arrival_richmond = S2 + D2 + 21
s.add(S3 >= arrival_richmond)  # Start meeting with Sandra after arrival
s.add(S3 >= sandra_start)
s.add(S3 + D3 <= sandra_end)  # Sandra's meeting must end by 21:45

if s.check() == sat:
    m = s.model()
    t0_val = m.eval(T0).as_long()
    s1_val = m.eval(S1).as_long()
    s2_val = m.eval(S2).as_long()
    s3_val = m.eval(S3).as_long()
    
    itinerary = [
        {"action": "meet", "person": "Jason", "start_time": min_to_time(s1_val), "end_time": min_to_time(s1_val + D1)},
        {"action": "meet", "person": "Jessica", "start_time": min_to_time(s2_val), "end_time": min_to_time(s2_val + D2)},
        {"action": "meet", "person": "Sandra", "start_time": min_to_time(s3_val), "end_time": min_to_time(s3_val + D3)}
    ]
    print(f'{{"itinerary": {itinerary}}}')
else:
    print('{"itinerary": []}')