import z3
import json

# Convert time in HH:MM to minutes
def time_to_min(time_str):
    parts = time_str.split(':')
    return int(parts[0]) * 60 + int(parts[1])

# Convert minutes back to HH:MM format
def min_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Define location names and their indices
loc_names = [
    "Pacific Heights",
    "Golden Gate Park",
    "The Castro",
    "Bayview",
    "Marina District",
    "Union Square",
    "Sunset District",
    "Alamo Square",
    "Financial District",
    "Mission District"
]

# Create a dictionary for travel times from the provided data
travel_data = """
Pacific Heights to Golden Gate Park: 15
Pacific Heights to The Castro: 16
Pacific Heights to Bayview: 22
Pacific Heights to Marina District: 6
Pacific Heights to Union Square: 12
Pacific Heights to Sunset District: 21
Pacific Heights to Alamo Square: 10
Pacific Heights to Financial District: 13
Pacific Heights to Mission District: 15
Golden Gate Park to Pacific Heights: 16
Golden Gate Park to The Castro: 13
Golden Gate Park to Bayview: 23
Golden Gate Park to Marina District: 16
Golden Gate Park to Union Square: 22
Golden Gate Park to Sunset District: 10
Golden Gate Park to Alamo Square: 9
Golden Gate Park to Financial District: 26
Golden Gate Park to Mission District: 17
The Castro to Pacific Heights: 16
The Castro to Golden Gate Park: 11
The Castro to Bayview: 19
The Castro to Marina District: 21
The Castro to Union Square: 19
The Castro to Sunset District: 17
The Castro to Alamo Square: 8
The Castro to Financial District: 21
The Castro to Mission District: 7
Bayview to Pacific Heights: 23
Bayview to Golden Gate Park: 22
Bayview to The Castro: 19
Bayview to Marina District: 27
Bayview to Union Square: 18
Bayview to Sunset District: 23
Bayview to Alamo Square: 16
Bayview to Financial District: 19
Bayview to Mission District: 13
Marina District to Pacific Heights: 7
Marina District to Golden Gate Park: 18
Marina District to The Castro: 22
Marina District to Bayview: 27
Marina District to Union Square: 16
Marina District to Sunset District: 19
Marina District to Alamo Square: 15
Marina District to Financial District: 17
Marina District to Mission District: 20
Union Square to Pacific Heights: 15
Union Square to Golden Gate Park: 22
Union Square to The Castro: 17
Union Square to Bayview: 15
Union Square to Marina District: 18
Union Square to Sunset District: 27
Union Square to Alamo Square: 15
Union Square to Financial District: 9
Union Square to Mission District: 14
Sunset District to Pacific Heights: 21
Sunset District to Golden Gate Park: 11
Sunset District to The Castro: 17
Sunset District to Bayview: 22
Sunset District to Marina District: 21
Sunset District to Union Square: 30
Sunset District to Alamo Square: 17
Sunset District to Financial District: 30
Sunset District to Mission District: 25
Alamo Square to Pacific Heights: 10
Alamo Square to Golden Gate Park: 9
Alamo Square to The Castro: 8
Alamo Square to Bayview: 16
Alamo Square to Marina District: 15
Alamo Square to Union Square: 14
Alamo Square to Sunset District: 16
Alamo Square to Financial District: 17
Alamo Square to Mission District: 10
Financial District to Pacific Heights: 13
Financial District to Golden Gate Park: 23
Financial District to The Castro: 20
Financial District to Bayview: 19
Financial District to Marina District: 15
Financial District to Union Square: 9
Financial District to Sunset District: 30
Financial District to Alamo Square: 17
Financial District to Mission District: 17
Mission District to Pacific Heights: 16
Mission District to Golden Gate Park: 17
Mission District to The Castro: 7
Mission District to Bayview: 14
Mission District to Marina District: 19
Mission District to Union Square: 15
Mission District to Sunset District: 24
Mission District to Alamo Square: 11
Mission District to Financial District: 15
"""

travel_dict = {}
lines = travel_data.strip().split('\n')
for line in lines:
    parts = line.split(' to ')
    if len(parts) < 2:
        continue
    from_loc = parts[0].strip()
    rest = parts[1].split(':')
    to_loc = rest[0].strip()
    time_val = int(rest[1].strip())
    travel_dict[(from_loc, to_loc)] = time_val

# Build a 10x10 travel time matrix
T = [[0]*10 for _ in range(10)]
for i in range(10):
    for j in range(10):
        if i == j:
            T[i][j] = 0
        else:
            from_name = loc_names[i]
            to_name = loc_names[j]
            T[i][j] = travel_dict.get((from_name, to_name), 10000)  # Default to a large number if not found

# Define meetings
meetings = [
    {"name": "Helen", "loc_index": 1, "start": time_to_min("09:30"), "end": time_to_min("12:15"), "min_duration": 45},
    {"name": "Steven", "loc_index": 2, "start": time_to_min("20:15"), "end": time_to_min("22:00"), "min_duration": 105},
    {"name": "Deborah", "loc_index": 3, "start": time_to_min("08:30"), "end": time_to_min("12:00"), "min_duration": 30},
    {"name": "Matthew", "loc_index": 4, "start": time_to_min("09:15"), "end": time_to_min("14:15"), "min_duration": 45},
    {"name": "Joseph", "loc_index": 5, "start": time_to_min("14:15"), "end": time_to_min("18:45"), "min_duration": 120},
    {"name": "Ronald", "loc_index": 6, "start": time_to_min("16:00"), "end": time_to_min("20:45"), "min_duration": 60},
    {"name": "Robert", "loc_index": 7, "start": time_to_min("18:30"), "end": time_to_min("21:15"), "min_duration": 120},
    {"name": "Rebecca", "loc_index": 8, "start": time_to_min("14:45"), "end": time_to_min("16:15"), "min_duration": 30},
    {"name": "Elizabeth", "loc_index": 9, "start": time_to_min("18:30"), "end": time_to_min("21:00"), "min_duration": 120}
]

# Set up Z3 solver
s = z3.Optimize()

# Define next_meeting variables: 9 steps
next_meeting = [z3.Int(f'next_{i}') for i in range(9)]

# Each next_meeting[i] is either -1 (skip) or a meeting index in [0,8]
for i in range(9):
    s.add(z3.Or(next_meeting[i] == -1, z3.And(next_meeting[i] >= 0, next_meeting[i] < 9)))

# If next_meeting[i] is -1, then all next must be -1
for i in range(8):
    s.add(z3.Implies(next_meeting[i] == -1, next_meeting[i+1] == -1))

# All non -1 next_meeting must be distinct
for i in range(9):
    for j in range(i+1, 9):
        s.add(z3.Implies(z3.And(next_meeting[i] != -1, next_meeting[j] != -1), next_meeting[i] != next_meeting[j]))

# Define start and end times for each meeting (0..8)
start = [z3.Int(f'start_{i}') for i in range(9)]
end = [z3.Int(f'end_{i}') for i in range(9)]

# active[meeting_id] indicates if the meeting is scheduled
active = [z3.Or([next_meeting[j] == i for j in range(9)]) for i in range(9)]

# Constraints for active meetings
for i in range(9):
    s.add(z3.Implies(active[i], start[i] >= meetings[i]["start"]))
    s.add(z3.Implies(active[i], end[i] == start[i] + meetings[i]["min_duration"]))
    s.add(z3.Implies(active[i], end[i] <= meetings[i]["end"]))

# Define arrays for current_time and location at each step (0 to 9)
current_time = [z3.Int(f'current_time_{i}') for i in range(10)]
location = [z3.Int(f'location_{i}') for i in range(10)]

# Step 0: start at Pacific Heights at 9:00 (540 minutes)
s.add(current_time[0] == 540)
s.add(location[0] == 0)  # Pacific Heights is index 0

# Propagate the sequence
for i in range(9):
    meeting_id = next_meeting[i]
    # If meeting_id is not -1, we schedule the meeting
    cond = (meeting_id != -1)
    # We'll compute the travel time from location[i] to the meeting's location
    # Since meeting_id is an integer expression, we create a nested condition for all possible meeting_id and location[i]
    travel_time = None
    for from_loc_val in range(10):
        for mid_val in range(9):
            to_loc_val = meetings[mid_val]["loc_index"]
            t_val = T[from_loc_val][to_loc_val]
            cond_inner = z3.And(location[i] == from_loc_val, meeting_id == mid_val)
            if travel_time is None:
                travel_time = t_val
            else:
                travel_time = z3.If(cond_inner, t_val, travel_time)
    if travel_time is None:
        travel_time = 0
    
    # The start time of the meeting must be at least current_time[i] + travel_time
    # But note: the meeting is identified by meeting_id, so we use start[meeting_id]
    s.add(z3.Implies(cond, start[meeting_id] >= current_time[i] + travel_time))
    
    # Also, we set the next state: current_time[i+1] = end[meeting_id] and location[i+1] = meetings[meeting_id]["loc_index"]
    # But since meeting_id is an expression, we do a similar thing for the next state
    next_time = z3.If(cond, end[meeting_id], current_time[i])
    next_loc = z3.If(cond, meetings[0]["loc_index"], location[i])  # dummy, we will overwrite
    # Build next_loc by cases
    for mid_val in range(9):
        next_loc = z3.If(z3.And(cond, meeting_id == mid_val), meetings[mid_val]["loc_index"], next_loc)
    # If not cond, next_loc remains location[i]
    next_loc = z3.If(cond, next_loc, location[i])
    
    s.add(current_time[i+1] == next_time)
    s.add(location[i+1] == next_loc)

# Objective: maximize the number of meetings scheduled
count_meetings = z3.Sum([z3.If(next_meeting[i] >= 0, 1, 0) for i in range(9)])
s.maximize(count_meetings)

# Solve
if s.check() == z3.sat:
    model = s.model()
    itinerary = []
    for i in range(9):
        next_val = model[next_meeting[i]].as_long()
        if next_val == -1:
            break
        meeting_id = next_val
        s_time = model[start[meeting_id]].as_long()
        e_time = model[end[meeting_id]].as_long()
        meeting_name = meetings[meeting_id]["name"]
        itinerary.append({
            "action": "meet",
            "person": meeting_name,
            "start_time": min_to_time(s_time),
            "end_time": min_to_time(e_time)
        })
    result = {"itinerary": itinerary}
    print("SOLUTION:")
    print(json.dumps(result, indent=2))
else:
    print("No solution found")