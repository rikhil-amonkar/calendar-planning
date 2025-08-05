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

# Start time at Pacific Heights: 9:00 AM
start_time = 9 * 60  # 540 minutes

# Define meeting start and end times in minutes
h_start = Int('h_start')
h_end = Int('h_end')
k_start = Int('k_start')
k_end = Int('k_end')
b_start = Int('b_start')
b_end = Int('b_end')

# Travel times in minutes
t_ph_to_nb = 9    # Pacific Heights to North Beach
t_nb_to_md = 18   # North Beach to Mission District
t_md_to_fd = 17   # Mission District to Financial District

# Constraints for Helen (North Beach: 9:00 AM to 5:00 PM)
s.add(h_start >= start_time + t_ph_to_nb)  # Arrive after travel
s.add(h_start >= 9 * 60)                  # Available from 9:00 AM
s.add(h_end >= h_start + 15)              # Minimum 15 minutes meeting
s.add(h_end <= 17 * 60)                   # Available until 5:00 PM

# Constraints for Kevin (Mission District: 10:45 AM to 2:45 PM)
s.add(k_start >= h_end + t_nb_to_md)      # Travel from North Beach to Mission District
s.add(k_start >= 10 * 60 + 45)            # Available from 10:45 AM
s.add(k_end >= k_start + 45)              # Minimum 45 minutes meeting
s.add(k_end <= 14 * 60 + 45)              # Available until 2:45 PM

# Constraints for Betty (Financial District: 7:00 PM to 9:45 PM)
s.add(b_start >= k_end + t_md_to_fd)      # Travel from Mission District to Financial District
s.add(b_start >= 19 * 60)                 # Available from 7:00 PM
s.add(b_end >= b_start + 90)              # Minimum 90 minutes meeting
s.add(b_end <= 21 * 60 + 45)              # Available until 9:45 PM

# Set meeting durations to minimum required
s.add(h_end == h_start + 15)
s.add(k_end == k_start + 45)
s.add(b_end == b_start + 90)

if s.check() == sat:
    m = s.model()
    h_start_val = m[h_start].as_long()
    h_end_val = m[h_end].as_long()
    k_start_val = m[k_start].as_long()
    k_end_val = m[k_end].as_long()
    b_start_val = m[b_start].as_long()
    b_end_val = m[b_end].as_long()
    
    itinerary = [
        {"action": "meet", "person": "Helen", "start_time": minutes_to_time(h_start_val), "end_time": minutes_to_time(h_end_val)},
        {"action": "meet", "person": "Kevin", "start_time": minutes_to_time(k_start_val), "end_time": minutes_to_time(k_end_val)},
        {"action": "meet", "person": "Betty", "start_time": minutes_to_time(b_start_val), "end_time": minutes_to_time(b_end_val)}
    ]
    result = {"itinerary": itinerary}
    print(json.dumps(result))
else:
    print('{"itinerary": []}')