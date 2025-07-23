from z3 import *

def parse_time(time_str):
    time_str = time_str.strip().upper()
    if time_str.endswith("PM"):
        time_str = time_str[:-2].strip()
        if ":" in time_str:
            hour, minute = time_str.split(":")
            hour = int(hour)
            if hour != 12:
                hour += 12
            total_minutes = hour * 60 + int(minute)
        else:
            hour = int(time_str)
            if hour != 12:
                hour += 12
            total_minutes = hour * 60
    else:
        time_str = time_str.replace("AM", "").strip()
        if ":" in time_str:
            hour, minute = time_str.split(":")
            hour = int(hour)
            total_minutes = hour * 60 + int(minute)
        else:
            total_minutes = int(time_str) * 60
    return total_minutes

travel_text = """
Chinatown to Embarcadero: 5
Chinatown to Pacific Heights: 10
Chinatown to Russian Hill: 7
Chinatown to Haight-Ashbury: 19
Chinatown to Golden Gate Park: 23
Chinatown to Fisherman's Wharf: 8
Chinatown to Sunset District: 29
Chinatown to The Castro: 22
Embarcadero to Chinatown: 7
Embarcadero to Pacific Heights: 11
Embarcadero to Russian Hill: 8
Embarcadero to Haight-Ashbury: 21
Embarcadero to Golden Gate Park: 25
Embarcadero to Fisherman's Wharf: 6
Embarcadero to Sunset District: 30
Embarcadero to The Castro: 25
Pacific Heights to Chinatown: 11
Pacific Heights to Embarcadero: 10
Pacific Heights to Russian Hill: 7
Pacific Heights to Haight-Ashbury: 11
Pacific Heights to Golden Gate Park: 15
Pacific Heights to Fisherman's Wharf: 13
Pacific Heights to Sunset District: 21
Pacific Heights to The Castro: 16
Russian Hill to Chinatown: 9
Russian Hill to Embarcadero: 8
Russian Hill to Pacific Heights: 7
Russian Hill to Haight-Ashbury: 17
Russian Hill to Golden Gate Park: 21
Russian Hill to Fisherman's Wharf: 7
Russian Hill to Sunset District: 23
Russian Hill to The Castro: 21
Haight-Ashbury to Chinatown: 19
Haight-Ashbury to Embarcadero: 20
Haight-Ashbury to Pacific Heights: 12
Haight-Ashbury to Russian Hill: 17
Haight-Ashbury to Golden Gate Park: 7
Haight-Ashbury to Fisherman's Wharf: 23
Haight-Ashbury to Sunset District: 15
Haight-Ashbury to The Castro: 6
Golden Gate Park to Chinatown: 23
Golden Gate Park to Embarcadero: 25
Golden Gate Park to Pacific Heights: 16
Golden Gate Park to Russian Hill: 19
Golden Gate Park to Haight-Ashbury: 7
Golden Gate Park to Fisherman's Wharf: 24
Golden Gate Park to Sunset District: 10
Golden Gate Park to The Castro: 13
Fisherman's Wharf to Chinatown: 12
Fisherman's Wharf to Embarcadero: 8
Fisherman's Wharf to Pacific Heights: 12
Fisherman's Wharf to Russian Hill: 7
Fisherman's Wharf to Haight-Ashbury: 22
Fisherman's Wharf to Golden Gate Park: 25
Fisherman's Wharf to Sunset District: 27
Fisherman's Wharf to The Castro: 27
Sunset District to Chinatown: 30
Sunset District to Embarcadero: 30
Sunset District to Pacific Heights: 21
Sunset District to Russian Hill: 24
Sunset District to Haight-Ashbury: 15
Sunset District to Golden Gate Park: 11
Sunset District to Fisherman's Wharf: 29
Sunset District to The Castro: 17
The Castro to Chinatown: 22
The Castro to Embarcadero: 22
The Castro to Pacific Heights: 16
The Castro to Russian Hill: 18
The Castro to Haight-Ashbury: 6
The Castro to Golden Gate Park: 11
The Castro to Fisherman's Wharf: 24
The Castro to Sunset District: 17
"""

travel_dict = {}
lines = travel_text.strip().split('\n')
for line in lines:
    if not line.strip():
        continue
    line = line.strip().rstrip('.')
    parts = line.split(':')
    if len(parts) < 2:
        continue
    time_val = int(parts[-1].strip())
    route = parts[0].strip()
    if " to " not in route:
        continue
    from_loc, to_loc = route.split(" to ")
    from_loc = from_loc.strip()
    to_loc = to_loc.strip()
    if from_loc not in travel_dict:
        travel_dict[from_loc] = {}
    travel_dict[from_loc][to_loc] = time_val

friend_names = ["Richard", "Mark", "Matthew", "Rebecca", "Melissa", "Margaret", "Emily", "George"]
friend_locations = ["Embarcadero", "Pacific Heights", "Russian Hill", "Haight-Ashbury", "Golden Gate Park", "Fisherman's Wharf", "Sunset District", "The Castro"]

available_start_str = ["3:15PM", "3:00PM", "5:30PM", "2:45PM", "1:45PM", "2:45PM", "3:45PM", "2:00PM"]
available_end_str = ["6:45PM", "5:00PM", "9:00PM", "6:00PM", "5:30PM", "8:15PM", "5:00PM", "4:15PM"]
min_duration_minutes = [90, 45, 90, 60, 90, 15, 45, 75]

base_minutes = 9 * 60  # 9:00 AM in minutes from midnight

available_start_minutes = []
available_end_minutes = []

for i in range(len(available_start_str)):
    start_minutes = parse_time(available_start_str[i]) - base_minutes
    end_minutes = parse_time(available_end_str[i]) - base_minutes
    available_start_minutes.append(start_minutes)
    available_end_minutes.append(end_minutes)

n = len(friend_names)
S = n  # index for the start node (Chinatown)

opt = Optimize()

meet = [Bool(f"meet_{i}") for i in range(n)]
t = [Real(f"t_{i}") for i in range(n)]
u = [Int(f"u_{i}") for i in range(n)]
next_var = [Int(f"next_{i}") for i in range(n+1)]  # n+1: includes start (index n)

total_meetings = Sum([If(meet[i], 1, 0) for i in range(n)])

# Start node constraints
opt.add(If(total_meetings > 0, Or([next_var[S] == j for j in range(n)]), next_var[S] == -1))

# If start points to j, then j must be met and have position 1
for j in range(n):
    opt.add(Implies(next_var[S] == j, meet[j]))
    opt.add(Implies(next_var[S] == j, u[j] == 1))

# Predecessor count constraint: each met friend has exactly one predecessor
for j in range(n):
    pred_count = Sum([If(And(meet[i], next_var[i] == j), 1, 0) for i in range(n)]) + If(next_var[S] == j, 1, 0)
    opt.add(Implies(meet[j], pred_count == 1))

# Meeting node constraints
for i in range(n):
    # Next must be valid (-1 or another meeting) and not self
    opt.add(Implies(meet[i], Or(next_var[i] == -1, *[next_var[i] == j for j in range(n) if j != i])))
    
    # Position constraints
    opt.add(If(meet[i], And(u[i] >= 1, u[i] <= total_meetings), u[i] == -1))
    
    # If next is j, then j must be met and u[j] = u[i] + 1
    for j in range(n):
        if i != j:
            opt.add(Implies(And(meet[i], next_var[i] == j), meet[j]))
            opt.add(Implies(And(meet[i], next_var[i] == j), u[j] == u[i] + 1))

# Meeting time constraints
for i in range(n):
    opt.add(Implies(meet[i],
             And(t[i] >= available_start_minutes[i],
                 t[i] + min_duration_minutes[i] <= available_end_minutes[i])))

# Travel time constraints
for j in range(n):
    opt.add(Implies(And(meet[j], next_var[S] == j),
             t[j] >= travel_dict["Chinatown"][friend_locations[j]]))

for i in range(n):
    for j in range(n):
        if i != j:
            opt.add(Implies(And(meet[i], meet[j], next_var[i] == j),
                         t[j] >= t[i] + min_duration_minutes[i] + travel_dict[friend_locations[i]][friend_locations[j]]))

# Maximize number of meetings
opt.maximize(total_meetings)

if opt.check() == sat:
    m = opt.model()
    meetings_scheduled = []
    for j in range(n):
        if is_true(m[meet[j]]):
            start_min = m[t[j]]
            # Convert Z3 Real to float
            if isinstance(start_min, FloatRef):
                start_val = start_min.numerator_as_long() / start_min.denominator_as_long()
            elif isinstance(start_min, IntNumRef):
                start_val = start_min.as_long()
            else:
                start_val = 0
            start_min_abs = start_val + base_minutes
            hours = int(start_min_abs) // 60
            minutes = int(start_min_abs) % 60
            start_time_str = f"{hours:02d}:{minutes:02d}"
            end_min = start_val + min_duration_minutes[j]
            end_min_abs = end_min + base_minutes
            hours_end = int(end_min_abs) // 60
            minutes_end = int(end_min_abs) % 60
            end_time_str = f"{hours_end:02d}:{minutes_end:02d}"
            meetings_scheduled.append({
                "action": "meet",
                "person": friend_names[j],
                "start_time": start_time_str,
                "end_time": end_time_str
            })
    # Sort chronologically
    meetings_scheduled.sort(key=lambda mtg: mtg['start_time'])
    print('SOLUTION:')
    print(f'{{"itinerary": {meetings_scheduled}}}')
else:
    print('SOLUTION:')
    print('{"itinerary": []}')