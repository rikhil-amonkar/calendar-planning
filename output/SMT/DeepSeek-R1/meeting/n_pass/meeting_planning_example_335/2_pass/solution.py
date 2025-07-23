from z3 import Int, Solver, sat
import json

def time_to_minutes(time_str):
    parts = time_str.split(':')
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

s = Solver()

# Define start times and end times for each meeting in minutes
k_start = Int('k_start')
k_end = Int('k_end')
h_start = Int('h_start')
h_end = Int('h_end')
b_start = Int('b_start')
b_end = Int('b_end')

# Start at Pacific Heights at 9:00 AM (540 minutes)
start_time = 540

# Travel times
t_ph_to_md = 15  # Pacific Heights to Mission District
t_md_to_nb = 17  # Mission District to North Beach
t_nb_to_fd = 8   # North Beach to Financial District

# Kevin's constraints (Mission District)
s.add(k_start >= start_time + t_ph_to_md)  # Arrive after travel
s.add(k_start >= 645)                     # Available from 10:45 AM
s.add(k_end == k_start + 45)              # Meeting duration
s.add(k_end <= 885)                       # Available until 2:45 PM

# Helen's constraints (North Beach)
s.add(h_start >= k_end + t_md_to_nb)      # Travel from Mission District to North Beach
s.add(h_end == h_start + 15)              # Meeting duration
s.add(h_end <= 1020)                      # Available until 5:00 PM

# Betty's constraints (Financial District)
s.add(b_start >= h_end + t_nb_to_fd)      # Travel from North Beach to Financial District
s.add(b_start >= 1140)                    # Available from 7:00 PM
s.add(b_end == b_start + 90)              # Meeting duration
s.add(b_end <= 1305)                      # Available until 9:45 PM

# Solve the constraints
if s.check() == sat:
    m = s.model()
    k_start_val = m[k_start].as_long()
    k_end_val = m[k_end].as_long()
    h_start_val = m[h_start].as_long()
    h_end_val = m[h_end].as_long()
    b_start_val = m[b_start].as_long()
    b_end_val = m[b_end].as_long()
    
    itinerary = [
        {"action": "meet", "person": "Kevin", "start_time": minutes_to_time(k_start_val), "end_time": minutes_to_time(k_end_val)},
        {"action": "meet", "person": "Helen", "start_time": minutes_to_time(h_start_val), "end_time": minutes_to_time(h_end_val)},
        {"action": "meet", "person": "Betty", "start_time": minutes_to_time(b_start_val), "end_time": minutes_to_time(b_end_val)}
    ]
    result = {"itinerary": itinerary}
    print(json.dumps(result))
else:
    print('{"itinerary": []}')