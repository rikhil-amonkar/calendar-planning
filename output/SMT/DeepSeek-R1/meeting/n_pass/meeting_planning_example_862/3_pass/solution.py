from z3 import *
import json

# Build travel_dict from travel_data
travel_data = """
Mission District to Alamo Square: 11
Mission District to Presidio: 25
Mission District to Russian Hill: 15
Mission District to North Beach: 17
Mission District to Golden Gate Park: 17
Mission District to Richmond District: 20
Mission District to Embarcadero: 19
Mission District to Financial District: 15
Mission District to Marina District: 19
Alamo Square to Mission District: 10
Alamo Square to Presidio: 17
Alamo Square to Russian Hill: 13
Alamo Square to North Beach: 15
Alamo Square to Golden Gate Park: 9
Alamo Square to Richmond District: 11
Alamo Square to Embarcadero: 16
Alamo Square to Financial District: 17
Alamo Square to Marina District: 15
Presidio to Mission District: 26
Presidio to Alamo Square: 19
Presidio to Russian Hill: 14
Presidio to North Beach: 18
Presidio to Golden Gate Park: 12
Presidio to Richmond District: 7
Presidio to Embarcadero: 20
Presidio to Financial District: 23
Presidio to Marina District: 11
Russian Hill to Mission District: 16
Russian Hill to Alamo Square: 15
Russian Hill to Presidio: 14
Russian Hill to North Beach: 5
Russian Hill to Golden Gate Park: 21
Russian Hill to Richmond District: 14
Russian Hill to Embarcadero: 8
Russian Hill to Financial District: 11
Russian Hill to Marina District: 7
North Beach to Mission District: 18
North Beach to Alamo Square: 16
North Beach to Presidio: 17
North Beach to Russian Hill: 4
North Beach to Golden Gate Park: 22
North Beach to Richmond District: 18
North Beach to Embarcadero: 6
North Beach to Financial District: 8
North Beach to Marina District: 9
Golden Gate Park to Mission District: 17
Golden Gate Park to Alamo Square: 9
Golden Gate Park to Presidio: 11
Golden Gate Park to Russian Hill: 19
Golden Gate Park to North Beach: 23
Golden Gate Park to Richmond District: 7
Golden Gate Park to Embarcadero: 25
Golden Gate Park to Financial District: 26
Golden Gate Park to Marina District: 16
Richmond District to Mission District: 20
Richmond District to Alamo Square: 13
Richmond District to Presidio: 7
Richmond District to Russian Hill: 13
Richmond District to North Beach: 17
Richmond District to Golden Gate Park: 9
Richmond District to Embarcadero: 19
Richmond District to Financial District: 22
Richmond District to Marina District: 9
Embarcadero to Mission District: 20
Embarcadero to Alamo Square: 19
Embarcadero to Presidio: 20
Embarcadero to Russian Hill: 8
Embarcadero to North Beach: 5
Embarcadero to Golden Gate Park: 25
Embarcadero to Richmond District: 21
Embarcadero to Financial District: 5
Embarcadero to Marina District: 12
Financial District to Mission District: 17
Financial District to Alamo Square: 17
Financial District to Presidio: 22
Financial District to Russian Hill: 11
Financial District to North Beach: 7
Financial District to Golden Gate Park: 23
Financial District to Richmond District: 21
Financial District to Embarcadero: 4
Financial District to Marina District: 15
Marina District to Mission District: 20
Marina District to Alamo Square: 15
Marina District to Presidio: 10
Marina District to Russian Hill: 8
Marina District to North Beach: 11
Marina District to Golden Gate Park: 18
Marina District to Richmond District: 11
Marina District to Embarcadero: 14
Marina District to Financial District: 17
"""

travel_dict = {}
lines = travel_data.strip().split('\n')
for line in lines:
    if not line:
        continue
    parts = line.split(':')
    if len(parts) < 2:
        continue
    time_part = parts[1].strip()
    if not time_part.isdigit():
        continue
    time_val = int(time_part)
    from_to_part = parts[0].strip()
    if ' to ' not in from_to_part:
        continue
    from_dist, to_dist = from_to_part.split(' to ', 1)
    from_dist = from_dist.strip()
    to_dist = to_dist.strip()
    travel_dict[(from_dist, to_dist)] = time_val

# List of friends and their details
friends = ["Laura", "Brian", "Karen", "Stephanie", "Helen", "Sandra", "Mary", "Deborah", "Elizabeth"]
locations = ["Alamo Square", "Presidio", "Russian Hill", "North Beach", "Golden Gate Park", "Richmond District", "Embarcadero", "Financial District", "Marina District"]
min_times = [75, 30, 90, 75, 120, 30, 120, 105, 105]  # in minutes

# Windows in minutes from 9:00 AM
windows = [
    ( (14*60+30) - 9*60, (16*60+15) - 9*60 ),   # Laura: 14:30-16:15 -> 330-435
    ( (10*60+15) - 9*60, (17*60) - 9*60 ),       # Brian: 10:15-17:00 -> 75-480
    ( (18*60) - 9*60, (20*60+15) - 9*60 ),        # Karen: 18:00-20:15 -> 540-675
    ( (10*60+15) - 9*60, (16*60) - 9*60 ),        # Stephanie: 10:15-16:00 -> 75-420
    ( (11*60+30) - 9*60, (21*60+45) - 9*60 ),      # Helen: 11:30-21:45 -> 150-765
    ( 0, (15*60+15) - 9*60 ),                      # Sandra: 9:00-15:15 -> 0-375
    ( (16*60+45) - 9*60, (18*60+45) - 9*60 ),      # Mary: 16:45-18:45 -> 465-585
    ( (19*60) - 9*60, (20*60+45) - 9*60 ),         # Deborah: 19:00-20:45 -> 600-705
    ( 0, (13*60+15) - 9*60 )                       # Elizabeth: 9:00-13:15 -> 0-255
]

# Build travel_time matrix for friends (9x9)
travel_time = [[0]*9 for _ in range(9)]
for i in range(9):
    for j in range(9):
        from_loc = locations[i]
        to_loc = locations[j]
        travel_time[i][j] = travel_dict.get((from_loc, to_loc), 1000)  # Default to a large number if not found

# Build travel_mission: travel from Mission District to each friend's location
travel_mission = [0] * 9
for i in range(9):
    to_loc = locations[i]
    travel_mission[i] = travel_dict.get(("Mission District", to_loc), 1000)

# Set up Z3 solver
s = Solver()

# k: number of meetings scheduled (0-9)
k = Int('k')
s.add(k >= 0, k <= 9)

# seq: sequence of meetings (size 9), each element is an integer in [0,8] if active, else -1
seq = [Int('seq_%d' % i) for i in range(9)]
for i in range(9):
    s.add(If(i < k, And(seq[i] >= 0, seq[i] < 9), seq[i] == -1))

# meet: boolean for each friend indicating if they are met
meet = [Bool('meet_%d' % i) for i in range(9)]

# start_seq: start time (minutes from 9:00) for each position in the sequence
start_seq = [Int('start_seq_%d' % i) for i in range(9)]

# Constraint: All active positions in seq are distinct
for i in range(9):
    for j in range(i+1, 9):
        s.add(Implies(And(i < k, j < k), seq[i] != seq[j]))

# Constraint: meet[i] is true iff friend i is in the sequence
for i in range(9):
    s.add(meet[i] == Or([And(seq[p] == i, p < k) for p in range(9)]))

# Define Z3 functions for travel_mission, travel_time, and min_times
# mission_travel_arr is a function from Int to Int
mission_travel_arr = Function('mission_travel_arr', IntSort(), IntSort())
for i in range(9):
    s.add(mission_travel_arr(i) == travel_mission[i])

# travel_arr is a function from (Int, Int) to Int
travel_arr = Function('travel_arr', IntSort(), IntSort(), IntSort())
for i in range(9):
    for j in range(9):
        s.add(travel_arr(i, j) == travel_time[i][j])

# min_times_arr is a function from Int to Int
min_times_arr = Function('min_times_arr', IntSort(), IntSort())
for i in range(9):
    s.add(min_times_arr(i) == min_times[i])

# Constraint: Window constraints for each meeting in the sequence
for p in range(9):
    for i in range(9):
        s.add(Implies(And(p < k, seq[p] == i),
                      And(start_seq[p] >= windows[i][0],
                          start_seq[p] + min_times[i] <= windows[i][1])))

# Travel constraints
# First meeting: start time >= travel time from Mission
s.add(Implies(k > 0, start_seq[0] >= mission_travel_arr(seq[0])))

# Consecutive meetings: start time of next meeting >= end time of current + travel time
for i in range(8):
    s.add(Implies(And(i+1 < k),
                  start_seq[i+1] >= start_seq[i] + min_times_arr(seq[i]) + travel_arr(seq[i], seq[i+1]) ))

# Maximize k
s.maximize(k)

# Check and get the solution
if s.check() == sat:
    m = s.model()
    k_val = m[k].as_long()
    itinerary = []
    for p in range(k_val):
        friend_idx = m[seq[p]].as_long()
        start_minutes = m[start_seq[p]].as_long()
        # Convert start_minutes to time string
        total_minutes = start_minutes
        hours_from_9 = total_minutes // 60
        minutes_remain = total_minutes % 60
        hours = 9 + hours_from_9
        minutes = minutes_remain
        start_time_str = f"{int(hours):02d}:{int(minutes):02d}"
        # Calculate end time
        end_minutes = start_minutes + min_times[friend_idx]
        hours_end = 9 + end_minutes // 60
        minutes_end = end_minutes % 60
        end_time_str = f"{int(hours_end):02d}:{int(minutes_end):02d}"
        person = friends[friend_idx]
        itinerary.append({
            "action": "meet",
            "person": person,
            "start_time": start_time_str,
            "end_time": end_time_str
        })
    # Output in JSON format
    result = {"itinerary": itinerary}
    print("SOLUTION:")
    print(json.dumps(result, indent=2))
else:
    print("No solution found")