from z3 import *

# Initialize solver
s = Solver()

# Define start and end times for each meeting (in minutes since midnight)
j_start, j_end = Int('j_start'), Int('j_end')  # Joseph
k_start, k_end = Int('k_start'), Int('k_end')  # Karen
kb_start, kb_end = Int('kb_start'), Int('kb_end')  # Kimberly
l_start, l_end = Int('l_start'), Int('l_end')  # Laura

# Joseph: Alamo Square, 11:30AM (690) to 12:45PM (765), min 15 minutes
s.add(j_start >= 690)
s.add(j_end <= 765)
s.add(j_end - j_start >= 15)

# Karen: Russian Hill, 2:30PM (870) to 7:45PM (1185), min 30 minutes
s.add(k_start >= 870)
s.add(k_end <= 1185)
s.add(k_end - k_start >= 30)

# Kimberly: North Beach, 3:45PM (945) to 7:15PM (1155), min 30 minutes
s.add(kb_start >= 945)
s.add(kb_end <= 1155)
s.add(kb_end - kb_start >= 30)

# Laura: The Castro, 7:45PM (1185) to 9:30PM (1290), min 105 minutes
s.add(l_start >= 1185)
s.add(l_end <= 1290)
s.add(l_end - l_start >= 105)

# Travel constraints
# Start at Fisherman's Wharf (9:00AM = 540 minutes) to Joseph (Alamo Square): 20 minutes
s.add(j_start >= 540 + 20)

# Joseph (Alamo Square) to Karen (Russian Hill): 13 minutes
s.add(k_start >= j_end + 13)

# Karen (Russian Hill) to Kimberly (North Beach): 5 minutes
s.add(kb_start >= k_end + 5)

# Kimberly (North Beach) to Laura (The Castro): 22 minutes
s.add(l_start >= kb_end + 22)

# Check for a feasible schedule
if s.check() == sat:
    m = s.model()
    j_start_val = m[j_start].as_long()
    j_end_val = m[j_end].as_long()
    k_start_val = m[k_start].as_long()
    k_end_val = m[k_end].as_long()
    kb_start_val = m[kb_start].as_long()
    kb_end_val = m[kb_end].as_long()
    l_start_val = m[l_start].as_long()
    l_end_val = m[l_end].as_long()
    
    # Convert minutes to HH:MM format
    def min_to_time(minutes):
        h = minutes // 60
        m = minutes % 60
        return f"{h:02d}:{m:02d}"
    
    itinerary = [
        {"action": "meet", "person": "Joseph", "start_time": min_to_time(j_start_val), "end_time": min_to_time(j_end_val)},
        {"action": "meet", "person": "Karen", "start_time": min_to_time(k_start_val), "end_time": min_to_time(k_end_val)},
        {"action": "meet", "person": "Kimberly", "start_time": min_to_time(kb_start_val), "end_time": min_to_time(kb_end_val)},
        {"action": "meet", "person": "Laura", "start_time": min_to_time(l_start_val), "end_time": min_to_time(l_end_val)}
    ]
    
    # Output the solution in JSON format
    print({
        "itinerary": itinerary
    })
else:
    print('No solution found')