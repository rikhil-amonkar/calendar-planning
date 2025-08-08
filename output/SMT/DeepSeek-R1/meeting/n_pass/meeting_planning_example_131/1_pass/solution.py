from z3 import *

def minutes_to_time(total_minutes):
    hours = total_minutes // 60
    minutes = total_minutes % 60
    return f"{hours:02d}:{minutes:02d}"

s = Solver()

t0 = Int('t0')
j_start = Int('j_start')
k_start = Int('k_start')

s.add(t0 >= 540)  # Departure from Pacific Heights after 9:00 AM
s.add(j_start >= 600)  # Jason available from 10:00 AM
s.add(j_start >= t0 + 11)  # Travel time to Presidio
s.add(j_start + 90 <= 975)  # Jason's meeting ends by 4:15 PM
s.add(k_start >= 930)  # Kenneth available from 3:30 PM
s.add(k_start >= j_start + 100)  # Travel after Jason's meeting (90 min + 10 min travel)
s.add(k_start + 45 <= 1005)  # Kenneth's meeting ends by 4:45 PM

if s.check() == sat:
    m = s.model()
    t0_val = m.eval(t0).as_long()
    j_start_val = m.eval(j_start).as_long()
    k_start_val = m.eval(k_start).as_long()
    
    j_end_val = j_start_val + 90
    k_end_val = k_start_val + 45
    
    itinerary = [
        {"action": "meet", "person": "Jason", "start_time": minutes_to_time(j_start_val), "end_time": minutes_to_time(j_end_val)},
        {"action": "meet", "person": "Kenneth", "start_time": minutes_to_time(k_start_val), "end_time": minutes_to_time(k_end_val)}
    ]
    result = {"itinerary": itinerary}
    print(f"SOLUTION: {result}")
else:
    print("No feasible schedule found.")