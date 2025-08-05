import json
from z3 import *

# Convert time string to minutes since 9:00 AM
def time_to_minutes(time_str):
    parts = time_str.split(':')
    hour = int(parts[0])
    minute = int(parts[1])
    total_minutes = (hour - 9) * 60 + minute if hour >= 9 else (hour + 24 - 9) * 60 + minute
    return total_minutes

# Travel time data as a multi-line string
travel_text = """
Bayview to North Beach: 22.
Bayview to Fisherman's Wharf: 25.
Bayview to Haight-Ashbury: 19.
Bayview to Nob Hill: 20.
Bayview to Golden Gate Park: 22.
Bayview to Union Square: 18.
Bayview to Alamo Square: 16.
Bayview to Presidio: 32.
Bayview to Chinatown: 19.
Bayview to Pacific Heights: 23.
North Beach to Bayview: 25.
North Beach to Fisherman's Wharf: 5.
North Beach to Haight-Ashbury: 18.
North Beach to Nob Hill: 7.
North Beach to Golden Gate Park: 22.
North Beach to Union Square: 7.
North Beach to Alamo Square: 16.
North Beach to Presidio: 17.
North Beach to Chinatown: 6.
North Beach to Pacific Heights: 8.
Fisherman's Wharf to Bayview: 26.
Fisherman's Wharf to North Beach: 6.
Fisherman's Wharf to Haight-Ashbury: 22.
Fisherman's Wharf to Nob Hill: 11.
Fisherman's Wharf to Golden Gate Park: 25.
Fisherman's Wharf to Union Square: 13.
Fisherman's Wharf to Alamo Square: 21.
Fisherman's Wharf to Presidio: 17.
Fisherman's Wharf to Chinatown: 12.
Fisherman's Wharf to Pacific Heights: 12.
Haight-Ashbury to Bayview: 18.
Haight-Ashbury to North Beach: 19.
Haight-Ashbury to Fisherman's Wharf: 23.
Haight-Ashbury to Nob Hill: 15.
Haight-Ashbury to Golden Gate Park: 7.
Haight-Ashbury to Union Square: 19.
Haight-Ashbury to Alamo Square: 5.
Haight-Ashbury to Presidio: 15.
Haight-Ashbury to Chinatown: 19.
Haight-Ashbury to Pacific Heights: 12.
Nob Hill to Bayview: 19.
Nob Hill to North Beach: 8.
Nob Hill to Fisherman's Wharf: 10.
Nob Hill to Haight-Ashbury: 13.
Nob Hill to Golden Gate Park: 17.
Nob Hill to Union Square: 7.
Nob Hill to Alamo Square: 11.
Nob Hill to Presidio: 17.
Nob Hill to Chinatown: 6.
Nob Hill to Pacific Heights: 8.
Golden Gate Park to Bayview: 23.
Golden Gate Park to North Beach: 23.
Golden Gate Park to Fisherman's Wharf: 24.
Golden Gate Park to Haight-Ashbury: 7.
Golden Gate Park to Nob Hill: 20.
Golden Gate Park to Union Square: 22.
Golden Gate Park to Alamo Square: 9.
Golden Gate Park to Presidio: 11.
Golden Gate Park to Chinatown: 23.
Golden Gate Park to Pacific Heights: 16.
Union Square to Bayview: 15.
Union Square to North Beach: 10.
Union Square to Fisherman's Wharf: 15.
Union Square to Haight-Ashbury: 18.
Union Square to Nob Hill: 9.
Union Square to Golden Gate Park: 22.
Union Square to Alamo Square: 15.
Union Square to Presidio: 24.
Union Square to Chinatown: 7.
Union Square to Pacific Heights: 15.
Alamo Square to Bayview: 16.
Alamo Square to North Beach: 15.
Alamo Square to Fisherman's Wharf: 19.
Alamo Square to Haight-Ashbury: 5.
Alamo Square to Nob Hill: 11.
Alamo Square to Golden Gate Park: 9.
Alamo Square to Union Square: 14.
Alamo Square to Presidio: 17.
Alamo Square to Chinatown: 15.
Alamo Square to Pacific Heights: 10.
Presidio to Bayview: 31.
Presidio to North Beach: 18.
Presidio to Fisherman's Wharf: 19.
Presidio to Haight-Ashbury: 15.
Presidio to Nob Hill: 18.
Presidio to Golden Gate Park: 12.
Presidio to Union Square: 22.
Presidio to Alamo Square: 19.
Presidio to Chinatown: 21.
Presidio to Pacific Heights: 11.
Chinatown to Bayview: 20.
Chinatown to North Beach: 3.
Chinatown to Fisherman's Wharf: 8.
Chinatown to Haight-Ashbury: 19.
Chinatown to Nob Hill: 9.
Chinatown to Golden Gate Park: 23.
Chinatown to Union Square: 7.
Chinatown to Alamo Square: 17.
Chinatown to Presidio: 19.
Chinatown to Pacific Heights: 10.
Pacific Heights to Bayview: 22.
Pacific Heights to North Beach: 9.
Pacific Heights to Fisherman's Wharf: 13.
Pacific Heights to Haight-Ashbury: 11.
Pacific Heights to Nob Hill: 8.
Pacific Heights to Golden Gate Park: 15.
Pacific Heights to Union Square: 12.
Pacific Heights to Alamo Square: 10.
Pacific Heights to Presidio: 11.
Pacific Heights to Chinatown: 11.
"""

# Parse travel_text to build travel_time_dict
travel_time_dict = {}
lines = travel_text.strip().split('\n')
for line in lines:
    if not line.strip():
        continue
    parts = line.split(':')
    from_to_str = parts[0].strip()
    time_val = int(parts[1].strip().rstrip('.'))
    locs = from_to_str.split(' to ')
    if len(locs) != 2:
        continue
    from_loc = locs[0].strip()
    to_loc = locs[1].strip()
    travel_time_dict[(from_loc, to_loc)] = time_val

# List of friends (excluding Matthew because we cannot meet him)
friends = [
    # (name, location, window_start_min, window_end_min, min_duration_min)
    ("Brian", "North Beach", time_to_minutes("13:00"), time_to_minutes("19:00"), 90),
    ("Richard", "Fisherman's Wharf", time_to_minutes("11:00"), time_to_minutes("12:45"), 60),
    ("Ashley", "Haight-Ashbury", time_to_minutes("15:00"), time_to_minutes("20:30"), 90),
    ("Elizabeth", "Nob Hill", time_to_minutes("11:45"), time_to_minutes("18:30"), 75),
    ("Jessica", "Golden Gate Park", time_to_minutes("20:00"), time_to_minutes("21:45"), 105),
    ("Deborah", "Union Square", time_to_minutes("17:30"), time_to_minutes("22:00"), 60),
    ("Kimberly", "Alamo Square", time_to_minutes("17:30"), time_to_minutes("21:15"), 45),
    ("Kenneth", "Chinatown", time_to_minutes("13:45"), time_to_minutes("19:30"), 105),
    ("Anthony", "Pacific Heights", time_to_minutes("14:15"), time_to_minutes("16:00"), 30)
]

# Initialize Z3 solver
s = Optimize()

n = len(friends)
meet = [Bool(f"meet_{i}") for i in range(n)]
start = [Int(f"start_{i}") for i in range(n)]
end = [Int(f"end_{i}") for i in range(n)]

# Constraints for each friend
for i in range(n):
    name, loc, win_start, win_end, dur = friends[i]
    # If meeting is scheduled, enforce constraints
    s.add(Implies(meet[i], start[i] >= win_start))
    s.add(Implies(meet[i], end[i] == start[i] + dur))
    s.add(Implies(meet[i], end[i] <= win_end))
    # Travel time from Bayview to the meeting location
    from_bayview = travel_time_dict[("Bayview", loc)]
    s.add(Implies(meet[i], start[i] >= from_bayview))

# Pairwise constraints for every pair of meetings
for i in range(n):
    for j in range(n):
        if i == j:
            continue
        loc_i = friends[i][1]
        loc_j = friends[j][1]
        travel_ij = travel_time_dict[(loc_i, loc_j)]
        travel_ji = travel_time_dict[(loc_j, loc_i)]
        cond1 = (end[i] + travel_ij <= start[j])
        cond2 = (end[j] + travel_ji <= start[i])
        s.add(Implies(And(meet[i], meet[j]), Or(cond1, cond2)))

# Maximize the number of meetings
total_meet = Sum([If(meet[i], 1, 0) for i in range(n)])
s.maximize(total_meet)

# Solve and output the schedule
if s.check() == sat:
    m = s.model()
    schedule = []
    for i in range(n):
        if is_true(m[meet[i]]):
            name = friends[i][0]
            start_val = m[start[i]].as_long()
            end_val = m[end[i]].as_long()
            # Convert minutes to time of day (from 9:00 AM)
            start_hour = 9 + start_val // 60
            start_minute = start_val % 60
            end_hour = 9 + end_val // 60
            end_minute = end_val % 60
            # Format as 24-hour time
            start_time = f"{start_hour:02d}:{start_minute:02d}"
            end_time = f"{end_hour:02d}:{end_minute:02d}"
            schedule.append({
                "action": "meet",
                "person": name,
                "start_time": start_time,
                "end_time": end_time
            })
    # Sort itinerary by start time
    schedule.sort(key=lambda x: x['start_time'])
    print('SOLUTION:')
    print(json.dumps({"itinerary": schedule}))
else:
    print('SOLUTION:')
    print('{"itinerary": []}')