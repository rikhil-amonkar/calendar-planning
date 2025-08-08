from z3 import *

def min_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

# Create solver
s = Solver()

# Define variables
m_start = Int('m_start')
m_end = Int('m_end')
e_start = Int('e_start')
e_end = Int('e_end')
n_start = Int('n_start')
n_end = Int('n_end')

# Constraints for Melissa
s.add(m_start >= 565)  # Arrival at Golden Gate Park at 9:25 AM (540 + 25 = 565 minutes)
s.add(m_end >= m_start + 15)  # Minimum meeting duration of 15 minutes
s.add(m_end <= 1200)  # Melissa available until 8:00 PM (1200 minutes)

# Travel from Golden Gate Park to Richmond District: 7 minutes
s.add(e_start == m_end + 7)
s.add(e_start >= 1005)  # Emily available from 4:45 PM (1005 minutes)

# Meeting with Emily: exactly 120 minutes
s.add(e_end == e_start + 120)

# Travel from Richmond District to Presidio: 7 minutes
s.add(e_end + 7 == 1185)  # Arrive at Presidio at 7:45 PM (1185 minutes)

# Meeting with Nancy
s.add(n_start == 1185)  # Start at 7:45 PM
s.add(n_end == n_start + 105)  # Meeting duration of 105 minutes
s.add(n_end <= 1320)  # Nancy available until 10:00 PM (1320 minutes)

# Minimize the start time for Melissa
s.minimize(m_start)

if s.check() == sat:
    model = s.model()
    m_start_val = model[m_start].as_long()
    m_end_val = model[m_end].as_long()
    e_start_val = model[e_start].as_long()
    e_end_val = model[e_end].as_long()
    n_start_val = model[n_start].as_long()
    n_end_val = model[n_end].as_long()
    
    itinerary = [
        {"action": "meet", "person": "Melissa", "start_time": min_to_time(m_start_val), "end_time": min_to_time(m_end_val)},
        {"action": "meet", "person": "Emily", "start_time": min_to_time(e_start_val), "end_time": min_to_time(e_end_val)},
        {"action": "meet", "person": "Nancy", "start_time": min_to_time(n_start_val), "end_time": min_to_time(n_end_val)}
    ]
    result = {"itinerary": itinerary}
    print(result)
else:
    print("No solution found")