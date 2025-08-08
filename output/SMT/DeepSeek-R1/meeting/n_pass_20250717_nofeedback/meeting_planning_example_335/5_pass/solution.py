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

# Define start times for each meeting in minutes
k_start = Int('k_start')
h_start = Int('h_start')
b_start = Int('b_start')

# Start at Pacific Heights at 9:00 AM (540 minutes)
start_time = 540

# Travel times
t_ph_to_md = 15  # Pacific Heights to Mission District
t_md_to_nb = 17  # Mission District to North Beach
t_nb_to_fd = 8   # North Beach to Financial District
t_fd_to_ph = 20  # Financial District to Pacific Heights

# Kevin's constraints (Mission District)
s.add(k_start >= start_time + t_ph_to_md)  # Arrive after travel
s.add(k_start >= time_to_minutes("10:45")) # Available from 10:45 AM
s.add(k_start + 45 <= time_to_minutes("14:45"))  # Meeting ends by 2:45 PM

# Helen's constraints (North Beach)
s.add(h_start >= k_start + 45 + t_md_to_nb)  # After Kevin's meeting + travel
s.add(h_start >= time_to_minutes("11:30"))   # Available from 11:30 AM
s.add(h_start + 15 <= time_to_minutes("17:00"))  # Meeting ends by 5:00 PM

# Betty's constraints (Financial District)
s.add(b_start >= h_start + 15 + t_nb_to_fd)  # After Helen's meeting + travel
s.add(b_start >= time_to_minutes("19:00"))   # Available from 7:00 PM
s.add(b_start + 90 <= time_to_minutes("21:45"))  # Meeting ends by 9:45 PM

# Return to Pacific Heights by 10:00 PM constraint
s.add(b_start + 90 + t_fd_to_ph <= time_to_minutes("22:00"))

# Solve the constraints
if s.check() == sat:
    m = s.model()
    k_start_val = m[k_start].as_long()
    h_start_val = m[h_start].as_long()
    b_start_val = m[b_start].as_long()
    
    itinerary = [
        {
            "action": "meet",
            "person": "Kevin",
            "start_time": minutes_to_time(k_start_val),
            "end_time": minutes_to_time(k_start_val + 45)
        },
        {
            "action": "meet",
            "person": "Helen",
            "start_time": minutes_to_time(h_start_val),
            "end_time": minutes_to_time(h_start_val + 15)
        },
        {
            "action": "meet",
            "person": "Betty",
            "start_time": minutes_to_time(b_start_val),
            "end_time": minutes_to_time(b_start_val + 90)
        }
    ]
    result = {"itinerary": itinerary}
    print(json.dumps(result))
else:
    print('{"itinerary": []}')