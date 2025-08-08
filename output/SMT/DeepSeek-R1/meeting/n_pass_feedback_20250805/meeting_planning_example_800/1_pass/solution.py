import json
from z3 import *

# Parse the travel times data
travel_data = """
Union Square to The Castro: 17.
Union Square to North Beach: 10.
Union Square to Embarcadero: 11.
Union Square to Alamo Square: 15.
Union Square to Nob Hill: 9.
Union Square to Presidio: 24.
Union Square to Fisherman's Wharf: 15.
Union Square to Mission District: 14.
Union Square to Haight-Ashbury: 18.
The Castro to Union Square: 19.
The Castro to North Beach: 20.
The Castro to Embarcadero: 22.
The Castro to Alamo Square: 8.
The Castro to Nob Hill: 16.
The Castro to Presidio: 20.
The Castro to Fisherman's Wharf: 24.
The Castro to Mission District: 7.
The Castro to Haight-Ashbury: 6.
North Beach to Union Square: 7.
North Beach to The Castro: 23.
North Beach to Embarcadero: 6.
North Beach to Alamo Square: 16.
North Beach to Nob Hill: 7.
North Beach to Presidio: 17.
North Beach to Fisherman's Wharf: 5.
North Beach to Mission District: 18.
North Beach to Haight-Ashbury: 18.
Embarcadero to Union Square: 10.
Embarcadero to The Castro: 25.
Embarcadero to North Beach: 5.
Embarcadero to Alamo Square: 19.
Embarcadero to Nob Hill: 10.
Embarcadero to Presidio: 20.
Embarcadero to Fisherman's Wharf: 6.
Embarcadero to Mission District: 20.
Embarcadero to Haight-Ashbury: 21.
Alamo Square to Union Square: 14.
Alamo Square to The Castro: 8.
Alamo Square to North Beach: 15.
Alamo Square to Embarcadero: 16.
Alamo Square to Nob Hill: 11.
Alamo Square to Presidio: 17.
Alamo Square to Fisherman's Wharf: 19.
Alamo Square to Mission District: 10.
Alamo Square to Haight-Ashbury: 5.
Nob Hill to Union Square: 7.
Nob Hill to The Castro: 17.
Nob Hill to North Beach: 8.
Nob Hill to Embarcadero: 9.
Nob Hill to Alamo Square: 11.
Nob Hill to Presidio: 17.
Nob Hill to Fisherman's Wharf: 10.
Nob Hill to Mission District: 13.
Nob Hill to Haight-Ashbury: 13.
Presidio to Union Square: 22.
Presidio to The Castro: 21.
Presidio to North Beach: 18.
Presidio to Embarcadero: 20.
Presidio to Alamo Square: 19.
Presidio to Nob Hill: 18.
Presidio to Fisherman's Wharf: 19.
Presidio to Mission District: 26.
Presidio to Haight-Ashbury: 15.
Fisherman's Wharf to Union Square: 13.
Fisherman's Wharf to The Castro: 27.
Fisherman's Wharf to North Beach: 6.
Fisherman's Wharf to Embarcadero: 8.
Fisherman's Wharf to Alamo Square: 21.
Fisherman's Wharf to Nob Hill: 11.
Fisherman's Wharf to Presidio: 17.
Fisherman's Wharf to Mission District: 22.
Fisherman's Wharf to Haight-Ashbury: 22.
Mission District to Union Square: 15.
Mission District to The Castro: 7.
Mission District to North Beach: 17.
Mission District to Embarcadero: 19.
Mission District to Alamo Square: 11.
Mission District to Nob Hill: 12.
Mission District to Presidio: 25.
Mission District to Fisherman's Wharf: 22.
Mission District to Haight-Ashbury: 12.
Haight-Ashbury to Union Square: 19.
Haight-Ashbury to The Castro: 6.
Haight-Ashbury to North Beach: 19.
Haight-Ashbury to Embarcadero: 20.
Haight-Ashbury to Alamo Square: 5.
Haight-Ashbury to Nob Hill: 15.
Haight-Ashbury to Presidio: 15.
Haight-Ashbury to Fisherman's Wharf: 23.
Haight-Ashbury to Mission District: 11.
"""

travel_times = {}
lines = travel_data.strip().split('.')
for line in lines:
    if not line.strip():
        continue
    parts = line.split(':')
    if len(parts) < 2:
        continue
    time_val = parts[1].strip()
    if time_val == '':
        continue
    time_val = int(time_val)
    locs_str = parts[0].strip()
    locs = locs_str.split(' to ')
    if len(locs) != 2:
        continue
    loc1 = locs[0].strip()
    loc2 = locs[1].strip()
    travel_times[(loc1, loc2)] = time_val

# Friends information: name, location, start_avail (minutes from 9:00 AM), end_avail, min_duration
friends_info = [
    {"name": "Melissa", "location": "The Castro", "start_avail": 675, "end_avail": 735, "duration": 30},
    {"name": "Kimberly", "location": "North Beach", "start_avail": 0, "end_avail": 90, "duration": 15},
    {"name": "Joseph", "location": "Embarcadero", "start_avail": 390, "end_avail": 630, "duration": 75},
    {"name": "Barbara", "location": "Alamo Square", "start_avail": 705, "end_avail": 765, "duration": 15},
    {"name": "Kenneth", "location": "Nob Hill", "start_avail": 195, "end_avail": 495, "duration": 105},
    {"name": "Joshua", "location": "Presidio", "start_avail": 450, "end_avail": 555, "duration": 105},
    {"name": "Brian", "location": "Fisherman's Wharf", "start_avail": 30, "end_avail": 390, "duration": 45},
    {"name": "Steven", "location": "Mission District", "start_avail": 630, "end_avail": 720, "duration": 90},
    {"name": "Betty", "location": "Haight-Ashbury", "start_avail": 600, "end_avail": 690, "duration": 90}
]

# Create Z3 solver and variables
opt = Optimize()
n = len(friends_info)
meet = [Bool(f"meet_{i}") for i in range(n)]
start_vars = [Real(f"start_{i}") for i in range(n)]

# Constraints for each friend
for i in range(n):
    info = friends_info[i]
    # Travel time from Union Square to this friend's location
    travel_from_start = travel_times[('Union Square', info['location'])]
    # If meeting this friend, start time must be >= travel_from_start and within availability window
    opt.add(Implies(meet[i], start_vars[i] >= travel_from_start))
    opt.add(Implies(meet[i], start_vars[i] >= info['start_avail']))
    opt.add(Implies(meet[i], start_vars[i] + info['duration'] <= info['end_avail']))

# Constraints for every pair of friends
for i in range(n):
    for j in range(i+1, n):
        loc_i = friends_info[i]['location']
        loc_j = friends_info[j]['location']
        travel_ij = travel_times.get((loc_i, loc_j))
        travel_ji = travel_times.get((loc_j, loc_i))
        if travel_ij is None or travel_ji is None:
            continue  # Skip if travel time not found (shouldn't happen)
        before_ij = Bool(f"before_{i}_{j}")
        # If both friends are met, enforce travel time constraint based on order
        opt.add(Implies(And(meet[i], meet[j]),
                      Or(
                          And(before_ij, start_vars[j] >= start_vars[i] + friends_info[i]['duration'] + travel_ij),
                          And(Not(before_ij), start_vars[i] >= start_vars[j] + friends_info[j]['duration'] + travel_ji)
                      )))

# Objective: maximize the number of meetings
total_meetings = Sum([If(meet[i], 1, 0) for i in range(n)])
opt.maximize(total_meetings)

# Solve and extract solution
schedule = []
if opt.check() == sat:
    model = opt.model()
    for i in range(n):
        if is_true(model.eval(meet[i])):
            s_val = model.eval(start_vars[i])
            if isinstance(s_val, RatNumRef):
                s_val = s_val.as_fraction()
            s_val = float(s_val)
            s_val_int = round(s_val)
            e_val_int = s_val_int + friends_info[i]['duration']
            # Convert to time string
            start_hour = 9 + s_val_int // 60
            start_minute = s_val_int % 60
            start_time = f"{int(start_hour):02d}:{int(start_minute):02d}"
            end_hour = 9 + e_val_int // 60
            end_minute = e_val_int % 60
            end_time = f"{int(end_hour):02d}:{int(end_minute):02d}"
            schedule.append({
                "action": "meet",
                "person": friends_info[i]['name'],
                "start_time": start_time,
                "end_time": end_time
            })
    # Sort meetings by start time
    schedule.sort(key=lambda x: x['start_time'])
else:
    schedule = []

# Output the solution
print("SOLUTION:")
print(json.dumps({"itinerary": schedule}))