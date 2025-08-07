from z3 import *

def min_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Initialize variables
J_start = Int('J_start')
J_end = Int('J_end')
K_start = Int('K_start')
K_end = Int('K_end')

s = Solver()

# Jason constraints: available from 10:00 (600) to 16:15 (975), duration >= 90
s.add(J_start >= 600)
s.add(J_end <= 975)
s.add(J_end - J_start >= 90)

# Kenneth constraints: available from 15:30 (930) to 16:45 (1005), duration = 45
s.add(K_start >= 930)
s.add(K_end == K_start + 45)
s.add(K_end <= 1005)

# Travel constraints
s.add(J_start >= 540 + 11)  # Depart Pacific Heights at 9:00, arrive Presidio at 9:11
s.add(K_start >= J_end + 10)  # Depart Presidio at J_end, arrive Marina at J_end + 10
s.add(K_start <= 960)  # Kenneth must start by 16:00 to have 45 minutes

# Check feasibility
if s.check() == sat:
    m = s.model()
    j_start_val = m[J_start].as_long()
    j_end_val = m[J_end].as_long()
    k_start_val = m[K_start].as_long()
    k_end_val = m[K_end].as_long()
    
    itinerary = [
        {"action": "meet", "person": "Jason", "start_time": min_to_time(j_start_val), "end_time": min_to_time(j_end_val)},
        {"action": "meet", "person": "Kenneth", "start_time": min_to_time(k_start_val), "end_time": min_to_time(k_end_val)}
    ]
    print('SOLUTION:')
    print(f'{{"itinerary": {itinerary}}}')
else:
    print("No feasible schedule found.")