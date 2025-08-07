from z3 import Optimize, Bool, Int, Implies, And, Or, If
import json

# Build travel_time_dict from the provided data
travel_time_data = """
Financial District to Fisherman's Wharf: 10.
Financial District to Presidio: 22.
Financial District to Bayview: 19.
Financial District to Haight-Ashbury: 19.
Financial District to Russian Hill: 11.
Financial District to The Castro: 20.
Financial District to Marina District: 15.
Financial District to Richmond District: 21.
Financial District to Union Square: 9.
Financial District to Sunset District: 30.
Fisherman's Wharf to Financial District: 11.
Fisherman's Wharf to Presidio: 17.
Fisherman's Wharf to Bayview: 26.
Fisherman's Wharf to Haight-Ashbury: 22.
Fisherman's Wharf to Russian Hill: 7.
Fisherman's Wharf to The Castro: 27.
Fisherman's Wharf to Marina District: 9.
Fisherman's Wharf to Richmond District: 18.
Fisherman's Wharf to Union Square: 13.
Fisherman's Wharf to Sunset District: 27.
Presidio to Financial District: 23.
Presidio to Fisherman's Wharf: 19.
Presidio to Bayview: 31.
Presidio to Haight-Ashbury: 15.
Presidio to Russian Hill: 14.
Presidio to The Castro: 21.
Presidio to Marina District: 11.
Presidio to Richmond District: 7.
Presidio to Union Square: 22.
Presidio to Sunset District: 15.
Bayview to Financial District: 19.
Bayview to Fisherman's Wharf: 25.
Bayview to Presidio: 32.
Bayview to Haight-Ashbury: 19.
Bayview to Russian Hill: 23.
Bayview to The Castro: 19.
Bayview to Marina District: 27.
Bayview to Richmond District: 25.
Bayview to Union Square: 18.
Bayview to Sunset District: 23.
Haight-Ashbury to Financial District: 21.
Haight-Ashbury to Fisherman's Wharf: 23.
Haight-Ashbury to Presidio: 15.
Haight-Ashbury to Bayview: 18.
Haight-Ashbury to Russian Hill: 17.
Haight-Ashbury to The Castro: 6.
Haight-Ashbury to Marina District: 17.
Haight-Ashbury to Richmond District: 10.
Haight-Ashbury to Union Square: 19.
Haight-Ashbury to Sunset District: 15.
Russian Hill to Financial District: 11.
Russian Hill to Fisherman's Wharf: 7.
Russian Hill to Presidio: 14.
Russian Hill to Bayview: 23.
Russian Hill to Haight-Ashbury: 17.
Russian Hill to The Castro: 21.
Russian Hill to Marina District: 7.
Russian Hill to Richmond District: 14.
Russian Hill to Union Square: 10.
Russian Hill to Sunset District: 23.
The Castro to Financial District: 21.
The Castro to Fisherman's Wharf: 24.
The Castro to Presidio: 20.
The Castro to Bayview: 19.
The Castro to Haight-Ashbury: 6.
The Castro to Russian Hill: 18.
The Castro to Marina District: 21.
The Castro to Richmond District: 16.
The Castro to Union Square: 19.
The Castro to Sunset District: 17.
Marina District to Financial District: 17.
Marina District to Fisherman's Wharf: 10.
Marina District to Presidio: 10.
Marina District to Bayview: 27.
Marina District to Haight-Ashbury: 16.
Marina District to Russian Hill: 8.
Marina District to The Castro: 22.
Marina District to Richmond District: 11.
Marina District to Union Square: 16.
Marina District to Sunset District: 19.
Richmond District to Financial District: 22.
Richmond District to Fisherman's Wharf: 18.
Richmond District to Presidio: 7.
Richmond District to Bayview: 27.
Richmond District to Haight-Ashbury: 10.
Richmond District to Russian Hill: 13.
Richmond District to The Castro: 16.
Richmond District to Marina District: 9.
Richmond District to Union Square: 21.
Richmond District to Sunset District: 11.
Union Square to Financial District: 9.
Union Square to Fisherman's Wharf: 15.
Union Square to Presidio: 24.
Union Square to Bayview: 15.
Union Square to Haight-Ashbury: 18.
Union Square to Russian Hill: 13.
Union Square to The Castro: 17.
Union Square to Marina District: 18.
Union Square to Richmond District: 20.
Union Square to Sunset District: 27.
Sunset District to Financial District: 30.
Sunset District to Fisherman's Wharf: 29.
Sunset District to Presidio: 16.
Sunset District to Bayview: 22.
Sunset District to Haight-Ashbury: 15.
Sunset District to Russian Hill: 24.
Sunset District to The Castro: 17.
Sunset District to Marina District: 21.
Sunset District to Richmond District: 12.
Sunset District to Union Square: 30.
"""

travel_time_dict = {}
lines = travel_time_data.strip().split('\n')
for line in lines:
    if not line:
        continue
    parts = line.split(':')
    if len(parts) < 2:
        continue
    time_part = parts[1].strip().rstrip('.')
    try:
        time_val = int(time_part)
    except:
        continue
    locs_part = parts[0].strip()
    if " to " not in locs_part:
        continue
    locs = locs_part.split(" to ")
    if len(locs) != 2:
        continue
    from_loc = locs[0].strip()
    to_loc = locs[1].strip()
    travel_time_dict[(from_loc, to_loc)] = time_val

# Define friends' information
friends_info = [
    {"name": "Mark", "location": "Fisherman's Wharf", "start_avail": 8*60+15, "end_avail": 10*60, "min_duration": 30},
    {"name": "Stephanie", "location": "Presidio", "start_avail": 12*60+15, "end_avail": 15*60, "min_duration": 75},
    {"name": "Betty", "location": "Bayview", "start_avail": 7*60+15, "end_avail": 20*60+30, "min_duration": 15},
    {"name": "Lisa", "location": "Haight-Ashbury", "start_avail": 15*60+30, "end_avail": 18*60+30, "min_duration": 45},
    {"name": "William", "location": "Russian Hill", "start_avail": 18*60+45, "end_avail": 20*60, "min_duration": 60},
    {"name": "Brian", "location": "The Castro", "start_avail": 9*60+15, "end_avail": 13*60+15, "min_duration": 30},
    {"name": "Joseph", "location": "Marina District", "start_avail": 10*60+45, "end_avail": 15*60, "min_duration": 90},
    {"name": "Ashley", "location": "Richmond District", "start_avail": 9*60+45, "end_avail": 11*60+15, "min_duration": 45},
    {"name": "Patricia", "location": "Union Square", "start_avail": 16*60+30, "end_avail": 20*60, "min_duration": 120},
    {"name": "Karen", "location": "Sunset District", "start_avail": 16*60+30, "end_avail": 22*60, "min_duration": 105}
]

# Add travel_from_start for each friend
start_loc = "Financial District"
for friend in friends_info:
    to_loc = friend['location']
    friend['travel_from_start'] = travel_time_dict[(start_loc, to_loc)]

# Initialize Z3 solver and variables
s = Optimize()
n = len(friends_info)
meet_vars = [Bool(f"meet_{i}") for i in range(n)]
s_vars = [Int(f"s_{i}") for i in range(n)]

# Add constraints
for i in range(n):
    friend = friends_info[i]
    s.add(Implies(meet_vars[i], 
                  And(
                      s_vars[i] >= friend['start_avail'],
                      s_vars[i] + friend['min_duration'] <= friend['end_avail'],
                      s_vars[i] >= 540 + friend['travel_from_start']  # 540 minutes = 9:00 AM
                  )))

# Pairwise constraints for meetings
for i in range(n):
    for j in range(i+1, n):
        loc_i = friends_info[i]['location']
        loc_j = friends_info[j]['location']
        travel_ij = travel_time_dict.get((loc_i, loc_j))
        travel_ji = travel_time_dict.get((loc_j, loc_i))
        if travel_ij is None or travel_ji is None:
            continue
        s.add(Implies(And(meet_vars[i], meet_vars[j]),
                      Or(
                          s_vars[i] + friends_info[i]['min_duration'] + travel_ij <= s_vars[j],
                          s_vars[j] + friends_info[j]['min_duration'] + travel_ji <= s_vars[i]
                      )))

# Maximize the number of meetings
s.maximize(Sum([If(meet_vars[i], 1, 0) for i in range(n)]))

# Solve and extract itinerary
itinerary = []
if s.check() == sat:
    m = s.model()
    for i in range(n):
        if m.evaluate(meet_vars[i]):
            friend = friends_info[i]
            start_minutes = m.evaluate(s_vars[i]).as_long()
            end_minutes = start_minutes + friend['min_duration']
            start_hour = start_minutes // 60
            start_minute = start_minutes % 60
            end_hour = end_minutes // 60
            end_minute = end_minutes % 60
            start_str = f"{start_hour:02d}:{start_minute:02d}"
            end_str = f"{end_hour:02d}:{end_minute:02d}"
            itinerary.append({
                "action": "meet",
                "person": friend['name'],
                "start_time": start_str,
                "end_time": end_str
            })
    # Sort itinerary by start_time
    itinerary.sort(key=lambda x: x['start_time'])
else:
    itinerary = []

# Output as JSON
result = {"itinerary": itinerary}
print("SOLUTION:")
print(json.dumps(result, indent=2))