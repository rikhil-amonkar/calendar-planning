from z3 import *
import json

# Define locations
locations = [
    "Embarcadero",          # 0
    "Fisherman's Wharf",    # 1
    "Financial District",   # 2
    "Russian Hill",         # 3
    "Marina District",      # 4
    "Richmond District",    # 5
    "Pacific Heights",      # 6
    "Haight-Ashbury",       # 7
    "Presidio",             # 8
    "Nob Hill",             # 9
    "The Castro"            # 10
]

# Travel data as a multi-line string
travel_str = """
Embarcadero to Fisherman's Wharf: 6
Embarcadero to Financial District: 5
Embarcadero to Russian Hill: 8
Embarcadero to Marina District: 12
Embarcadero to Richmond District: 21
Embarcadero to Pacific Heights: 11
Embarcadero to Haight-Ashbury: 21
Embarcadero to Presidio: 20
Embarcadero to Nob Hill: 10
Embarcadero to The Castro: 25
Fisherman's Wharf to Embarcadero: 8
Fisherman's Wharf to Financial District: 11
Fisherman's Wharf to Russian Hill: 7
Fisherman's Wharf to Marina District: 9
Fisherman's Wharf to Richmond District: 18
Fisherman's Wharf to Pacific Heights: 12
Fisherman's Wharf to Haight-Ashbury: 22
Fisherman's Wharf to Presidio: 17
Fisherman's Wharf to Nob Hill: 11
Fisherman's Wharf to The Castro: 27
Financial District to Embarcadero: 4
Financial District to Fisherman's Wharf: 10
Financial District to Russian Hill: 11
Financial District to Marina District: 15
Financial District to Richmond District: 21
Financial District to Pacific Heights: 13
Financial District to Haight-Ashbury: 19
Financial District to Presidio: 22
Financial District to Nob Hill: 8
Financial District to The Castro: 20
Russian Hill to Embarcadero: 8
Russian Hill to Fisherman's Wharf: 7
Russian Hill to Financial District: 11
Russian Hill to Marina District: 7
Russian Hill to Richmond District: 14
Russian Hill to Pacific Heights: 7
Russian Hill to Haight-Ashbury: 17
Russian Hill to Presidio: 14
Russian Hill to Nob Hill: 5
Russian Hill to The Castro: 21
Marina District to Embarcadero: 14
Marina District to Fisherman's Wharf: 10
Marina District to Financial District: 17
Marina District to Russian Hill: 8
Marina District to Richmond District: 11
Marina District to Pacific Heights: 7
Marina District to Haight-Ashbury: 16
Marina District to Presidio: 10
Marina District to Nob Hill: 12
Marina District to The Castro: 22
Richmond District to Embarcadero: 19
Richmond District to Fisherman's Wharf: 18
Richmond District to Financial District: 22
Richmond District to Russian Hill: 13
Richmond District to Marina District: 9
Richmond District to Pacific Heights: 10
Richmond District to Haight-Ashbury: 10
Richmond District to Presidio: 7
Richmond District to Nob Hill: 17
Richmond District to The Castro: 16
Pacific Heights to Embarcadero: 10
Pacific Heights to Fisherman's Wharf: 13
Pacific Heights to Financial District: 13
Pacific Heights to Russian Hill: 7
Pacific Heights to Marina District: 6
Pacific Heights to Richmond District: 12
Pacific Heights to Haight-Ashbury: 11
Pacific Heights to Presidio: 11
Pacific Heights to Nob Hill: 8
Pacific Heights to The Castro: 16
Haight-Ashbury to Embarcadero: 20
Haight-Ashbury to Fisherman's Wharf: 23
Haight-Ashbury to Financial District: 21
Haight-Ashbury to Russian Hill: 17
Haight-Ashbury to Marina District: 17
Haight-Ashbury to Richmond District: 10
Haight-Ashbury to Pacific Heights: 12
Haight-Ashbury to Presidio: 15
Haight-Ashbury to Nob Hill: 15
Haight-Ashbury to The Castro: 6
Presidio to Embarcadero: 20
Presidio to Fisherman's Wharf: 19
Presidio to Financial District: 23
Presidio to Russian Hill: 14
Presidio to Marina District: 11
Presidio to Richmond District: 7
Presidio to Pacific Heights: 11
Presidio to Haight-Ashbury: 15
Presidio to Nob Hill: 18
Presidio to The Castro: 21
Nob Hill to Embarcadero: 9
Nob Hill to Fisherman's Wharf: 10
Nob Hill to Financial District: 9
Nob Hill to Russian Hill: 5
Nob Hill to Marina District: 11
Nob Hill to Richmond District: 14
Nob Hill to Pacific Heights: 8
Nob Hill to Haight-Ashbury: 13
Nob Hill to Presidio: 17
Nob Hill to The Castro: 17
The Castro to Embarcadero: 22
The Castro to Fisherman's Wharf: 24
The Castro to Financial District: 21
The Castro to Russian Hill: 18
The Castro to Marina District: 21
The Castro to Richmond District: 16
The Castro to Pacific Heights: 16
The Castro to Haight-Ashbury: 6
The Castro to Presidio: 20
The Castro to Nob Hill: 16
"""

# Parse travel_str to build travel_dict
travel_dict = {}
lines = travel_str.strip().split('\n')
for line in lines:
    line = line.strip()
    if not line:
        continue
    parts = line.split(':')
    time_val = int(parts[-1].strip())
    route_part = parts[0].strip()
    if ' to ' in route_part:
        from_place, to_place = route_part.split(' to ')
        from_place = from_place.strip()
        to_place = to_place.strip()
        travel_dict[(from_place, to_place)] = time_val

# Build T: 11x11 travel time matrix
T = [[0]*11 for _ in range(11)]
for i in range(11):
    for j in range(11):
        if i == j:
            T[i][j] = 0
        else:
            key = (locations[i], locations[j])
            T[i][j] = travel_dict.get(key, 10000)  # 10000 as a large penalty if not found (should not happen)

# Friend data: names, available_start, available_end, min_duration
friend_names = [
    "Stephanie",    # at Fisherman's Wharf (location1)
    "Lisa",         # at Financial District (location2)
    "Melissa",      # at Russian Hill (location3)
    "Betty",        # at Marina District (location4)
    "Sarah",        # at Richmond District (location5)
    "Daniel",       # at Pacific Heights (location6)
    "Joshua",       # at Haight-Ashbury (location7)
    "Joseph",       # at Presidio (location8)
    "Andrew",       # at Nob Hill (location9)
    "John"          # at The Castro (location10)
]

# Convert available times to minutes from 9:00 AM
# Format: [start, end] in minutes from 9:00 AM
available_start = [
    390,    # Stephanie: 3:30PM (15:30) -> 15*60+30 - 9*60 = 930-540=390
    105,    # Lisa: 10:45AM -> 10*60+45 - 9*60 = 645-540=105
    480,    # Melissa: 5:00PM (17:00) -> 17*60 - 9*60 = 1020-540=480
    105,    # Betty: 10:45AM -> 645-540=105
    435,    # Sarah: 4:15PM (16:15) -> 16*60+15 - 540 = 975-540=435
    570,    # Daniel: 6:30PM (18:30) -> 18*60+30 - 540 = 1110-540=570
    0,      # Joshua: 9:00AM -> 0
    0,      # Joseph: 7:00AM -> max(0, 420-540)=0, but available from 9:00AM
    645,    # Andrew: 7:45PM (19:45) -> 19*60+45 - 540 = 1185-540=645
    255     # John: 1:15PM (13:15) -> 13*60+15 - 540 = 795-540=255
]
available_end = [
    780,    # Stephanie: 10:00PM (22:00) -> 22*60 - 540 = 1320-540=780
    495,    # Lisa: 5:15PM (17:15) -> 17*60+15 - 540 = 1035-540=495
    765,    # Melissa: 9:45PM (21:45) -> 21*60+45 - 540 = 1305-540=765
    315,    # Betty: 2:15PM (14:15) -> 14*60+15 - 540 = 855-540=315
    630,    # Sarah: 7:30PM (19:30) -> 19*60+30 - 540 = 1170-540=630
    765,    # Daniel: 9:45PM (21:45) -> 21*60+45 - 540 = 1305-540=765
    390,    # Joshua: 3:30PM (15:30) -> 15*60+30 - 540 = 930-540=390
    240,    # Joseph: 1:00PM (13:00) -> 13*60 - 540 = 780-540=240
    780,    # Andrew: 10:00PM (22:00) -> 22*60 - 540 = 1320-540=780
    645     # John: 7:45PM (19:45) -> 19*60+45 - 540 = 1185-540=645
]
min_duration = [30, 15, 120, 60, 105, 60, 15, 45, 105, 45]

# Set up Z3 solver
s = Optimize()
s.set("timeout", 300000)  # 5 minutes timeout in milliseconds

# There are 10 friends (indexed 0 to 9)
# visit[k] : whether we meet friend k
visit = [Bool(f'visit_{k}') for k in range(10)]
# t[k] : start time of meeting with friend k (in minutes from 9:00 AM)
t = [Int(f't_{k}') for k in range(10)]
# u[k] : arrival time at the location of friend k (before waiting for the window to open)
u = [Int(f'u_{k}') for k in range(10)]

# x[i][k] : we travel from node i (which is the start node0 or a friend node, which is location i) to friend k (which is location k+1)
# Note: node0: start (Embarcadero), node1: friend0 (Stephanie), ... node10: friend9 (John)
x = [[Bool(f'x_{i}_{k}') for k in range(10)] for i in range(11)]

# Add constraints: no self-loop: if i = k+1, then x[i][k] must be false
for i in range(11):
    for k in range(10):
        if i == k+1:
            s.add(Not(x[i][k]))

# Start: out_degree0 = sum_{k} x[0][k] 
out_degree0 = Sum([x[0][k] for k in range(10)])
s.add(out_degree0 <= 1)
s.add(out_degree0 == If(Or(visit), 1, 0))  # Or(visit) is Or(visit[0], visit[1], ...)

# For each friend k: in_degree_k = sum_{i} x[i][k] 
in_degree = [Sum([x[i][k] for i in range(11)]) for k in range(10)]
for k in range(10):
    s.add(in_degree[k] == visit[k])

# For each friend k: out_degree_k = sum_{j} x[k+1][j] 
for k in range(10):
    out_degree_k = Sum([x[k+1][j] for j in range(10)])
    s.add(out_degree_k <= 1)

# Total edges = sum_{i,k} x[i][k] = number of visited friends (since each visited friend has one incoming edge)
total_edges = Sum([x[i][k] for i in range(11) for k in range(10)])
s.add(total_edges == Sum([If(visit[k], 1, 0) for k in range(10)]))

# Time constraints for each friend k
for k in range(10):
    s.add(u[k] >= 0)
    s.add(t[k] >= u[k])
    s.add(t[k] >= available_start[k])
    s.add(t[k] + min_duration[k] <= available_end[k])

# Travel constraints
for i in range(11):
    for k in range(10):
        if i == k+1:
            continue  # already handled by self-loop constraint
        if i == 0:
            # Travel from start (node0) to friend k (node k+1): travel time T[0][k+1]
            s.add(If(x[i][k], u[k] >= 0 + T[0][k+1], True))
        else:
            # Travel from node i (which is the location of friend j, where j = i-1) to friend k (node k+1)
            j = i-1   # j is the friend index for the source node i
            # The meeting at friend j ends at t[j] + min_duration[j]
            s.add(If(x[i][k], u[k] >= t[j] + min_duration[j] + T[i][k+1], True))

# Maximize the number of friends visited
total_visits = Sum([If(visit[k], 1, 0) for k in range(10)])
s.maximize(total_visits)

# Solve
if s.check() == sat:
    m = s.model()
    # Collect the meetings
    itinerary = []
    for k in range(10):
        if m.evaluate(visit[k]):
            start_val = m.evaluate(t[k])
            if isinstance(start_val, IntNumRef):
                start_minutes = start_val.as_long()
                # Convert to time from 9:00 AM
                total_minutes = start_minutes
                hours = 9 + total_minutes // 60
                minutes = total_minutes % 60
                start_time = f"{hours:02d}:{minutes:02d}"
                # End time = start + min_duration
                end_minutes = start_minutes + min_duration[k]
                hours_end = 9 + end_minutes // 60
                minutes_end = end_minutes % 60
                end_time = f"{hours_end:02d}:{minutes_end:02d}"
                itinerary.append({
                    "action": "meet",
                    "person": friend_names[k],
                    "start_time": start_time,
                    "end_time": end_time
                })
    # Sort by start_time
    itinerary.sort(key=lambda x: x['start_time'])
    # Output as JSON
    result = {"itinerary": itinerary}
    print("SOLUTION:")
    print(json.dumps(result, indent=2))
else:
    print("No solution found")