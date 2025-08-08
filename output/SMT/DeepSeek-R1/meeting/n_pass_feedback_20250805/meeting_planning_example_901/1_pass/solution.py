from z3 import *
import json

travel_text = """Russian Hill to Pacific Heights: 7.
Russian Hill to North Beach: 5.
Russian Hill to Golden Gate Park: 21.
Russian Hill to Embarcadero: 8.
Russian Hill to Haight-Ashbury: 17.
Russian Hill to Fisherman's Wharf: 7.
Russian Hill to Mission District: 16.
Russian Hill to Alamo Square: 15.
Russian Hill to Bayview: 23.
Russian Hill to Richmond District: 14.
Pacific Heights to Russian Hill: 7.
Pacific Heights to North Beach: 9.
Pacific Heights to Golden Gate Park: 15.
Pacific Heights to Embarcadero: 10.
Pacific Heights to Haight-Ashbury: 11.
Pacific Heights to Fisherman's Wharf: 13.
Pacific Heights to Mission District: 15.
Pacific Heights to Alamo Square: 10.
Pacific Heights to Bayview: 22.
Pacific Heights to Richmond District: 12.
North Beach to Russian Hill: 4.
North Beach to Pacific Heights: 8.
North Beach to Golden Gate Park: 22.
North Beach to Embarcadero: 6.
North Beach to Haight-Ashbury: 18.
North Beach to Fisherman's Wharf: 5.
North Beach to Mission District: 18.
North Beach to Alamo Square: 16.
North Beach to Bayview: 25.
North Beach to Richmond District: 18.
Golden Gate Park to Russian Hill: 19.
Golden Gate Park to Pacific Heights: 16.
Golden Gate Park to North Beach: 23.
Golden Gate Park to Embarcadero: 25.
Golden Gate Park to Haight-Ashbury: 7.
Golden Gate Park to Fisherman's Wharf: 24.
Golden Gate Park to Mission District: 17.
Golden Gate Park to Alamo Square: 9.
Golden Gate Park to Bayview: 23.
Golden Gate Park to Richmond District: 7.
Embarcadero to Russian Hill: 8.
Embarcadero to Pacific Heights: 11.
Embarcadero to North Beach: 5.
Embarcadero to Golden Gate Park: 25.
Embarcadero to Haight-Ashbury: 21.
Embarcadero to Fisherman's Wharf: 6.
Embarcadero to Mission District: 20.
Embarcadero to Alamo Square: 19.
Embarcadero to Bayview: 21.
Embarcadero to Richmond District: 21.
Haight-Ashbury to Russian Hill: 17.
Haight-Ashbury to Pacific Heights: 12.
Haight-Ashbury to North Beach: 19.
Haight-Ashbury to Golden Gate Park: 7.
Haight-Ashbury to Embarcadero: 20.
Haight-Ashbury to Fisherman's Wharf: 23.
Haight-Ashbury to Mission District: 11.
Haight-Ashbury to Alamo Square: 5.
Haight-Ashbury to Bayview: 18.
Haight-Ashbury to Richmond District: 10.
Fisherman's Wharf to Russian Hill: 7.
Fisherman's Wharf to Pacific Heights: 12.
Fisherman's Wharf to North Beach: 6.
Fisherman's Wharf to Golden Gate Park: 25.
Fisherman's Wharf to Embarcadero: 8.
Fisherman's Wharf to Haight-Ashbury: 22.
Fisherman's Wharf to Mission District: 22.
Fisherman's Wharf to Alamo Square: 21.
Fisherman's Wharf to Bayview: 26.
Fisherman's Wharf to Richmond District: 18.
Mission District to Russian Hill: 15.
Mission District to Pacific Heights: 16.
Mission District to North Beach: 17.
Mission District to Golden Gate Park: 17.
Mission District to Embarcadero: 19.
Mission District to Haight-Ashbury: 12.
Mission District to Fisherman's Wharf: 22.
Mission District to Alamo Square: 11.
Mission District to Bayview: 14.
Mission District to Richmond District: 20.
Alamo Square to Russian Hill: 13.
Alamo Square to Pacific Heights: 10.
Alamo Square to North Beach: 15.
Alamo Square to Golden Gate Park: 9.
Alamo Square to Embarcadero: 16.
Alamo Square to Haight-Ashbury: 5.
Alamo Square to Fisherman's Wharf: 19.
Alamo Square to Mission District: 10.
Alamo Square to Bayview: 16.
Alamo Square to Richmond District: 11.
Bayview to Russian Hill: 23.
Bayview to Pacific Heights: 23.
Bayview to North Beach: 22.
Bayview to Golden Gate Park: 22.
Bayview to Embarcadero: 19.
Bayview to Haight-Ashbury: 19.
Bayview to Fisherman's Wharf: 25.
Bayview to Mission District: 13.
Bayview to Alamo Square: 16.
Bayview to Richmond District: 25.
Richmond District to Russian Hill: 13.
Richmond District to Pacific Heights: 10.
Richmond District to North Beach: 17.
Richmond District to Golden Gate Park: 9.
Richmond District to Embarcadero: 19.
Richmond District to Haight-Ashbury: 10.
Richmond District to Fisherman's Wharf: 18.
Richmond District to Mission District: 20.
Richmond District to Alamo Square: 13.
Richmond District to Bayview: 27."""

travel_dict = {}
lines = travel_text.strip().split('.')
for line in lines:
    line = line.strip()
    if not line:
        continue
    if ':' not in line:
        continue
    parts = line.split(':', 1)
    route = parts[0].strip()
    time_str = parts[1].strip()
    try:
        time_val = int(time_str)
    except:
        time_val = int(time_str.split()[0])
    if ' to ' not in route:
        continue
    from_loc, to_loc = route.split(' to ', 1)
    from_loc = from_loc.strip()
    to_loc = to_loc.strip()
    travel_dict[(from_loc, to_loc)] = time_val

meetings = [
    {"name": "Emily", "location": "Pacific Heights", "window_start": 15, "window_end": 285, "min_duration": 120},
    {"name": "Helen", "location": "North Beach", "window_start": 285, "window_end": 585, "min_duration": 30},
    {"name": "Kimberly", "location": "Golden Gate Park", "window_start": 585, "window_end": 735, "min_duration": 75},
    {"name": "James", "location": "Embarcadero", "window_start": 90, "window_end": 150, "min_duration": 30},
    {"name": "Linda", "location": "Haight-Ashbury", "window_start": 0, "window_end": 615, "min_duration": 15},
    {"name": "Paul", "location": "Fisherman's Wharf", "window_start": 345, "window_end": 585, "min_duration": 90},
    {"name": "Anthony", "location": "Mission District", "window_start": 0, "window_end": 345, "min_duration": 105},
    {"name": "Nancy", "location": "Alamo Square", "window_start": 0, "window_end": 285, "min_duration": 120},
    {"name": "William", "location": "Bayview", "window_start": 510, "window_end": 690, "min_duration": 120},
    {"name": "Margaret", "location": "Richmond District", "window_start": 375, "window_end": 555, "min_duration": 45},
]

loc_names = [m["location"] for m in meetings]
names = [m["name"] for m in meetings]
window_start_list = [m["window_start"] for m in meetings]
window_end_list = [m["window_end"] for m in meetings]
min_duration_list = [m["min_duration"] for m in meetings]

start_travel = []
for loc in loc_names:
    start_travel.append(travel_dict[("Russian Hill", loc)])

travel_between = []
for i in range(10):
    row = []
    for j in range(10):
        from_loc = loc_names[i]
        to_loc = loc_names[j]
        row.append(travel_dict[(from_loc, to_loc)])
    travel_between.append(row)

active = [Bool(f'active_{i}') for i in range(10)]
next_start = [Bool(f'next_start_{j}') for j in range(10)]
next_meeting = [[Bool(f'next_{i}_{j}') for j in range(10)] for i in range(10)]
start_time = [Int(f'start_{i}') for i in range(10)]

s = Solver()
opt = Optimize()

for j in range(10):
    s.add(Implies(next_start[j], active[j]))
    for i in range(10):
        s.add(Implies(next_meeting[i][j], And(active[i], active[j])))
        if i == j:
            s.add(Not(next_meeting[i][j]))

for j in range(10):
    incoming = [next_start[j]]
    for i in range(10):
        incoming.append(next_meeting[i][j])
    s.add(active[j] == Or(incoming))
    s.add(If(active[j], Sum([If(x, 1, 0) for x in incoming]) == 1, True))

for i in range(10):
    outgoing = [next_meeting[i][j] for j in range(10)]
    s.add(Implies(active[i], Sum([If(x, 1, 0) for x in outgoing]) <= 1))

s.add(Sum([If(next_start[j], 1, 0) for j in range(10)]) <= 1)
active_count = Sum([If(active[i], 1, 0) for i in range(10)])
s.add(Sum([If(next_start[j], 1, 0) for j in range(10)]) == If(active_count > 0, 1, 0))

for j in range(10):
    conditions = [next_start[j]]
    values = [start_travel[j]]
    for i in range(10):
        conditions.append(next_meeting[i][j])
        values.append(start_time[i] + min_duration_list[i] + travel_between[i][j])
    arrival_j = 0
    for idx in range(len(conditions)):
        arrival_j = If(conditions[idx], values[idx], arrival_j)
    s.add(Implies(active[j], start_time[j] >= arrival_j))
    s.add(Implies(active[j], start_time[j] >= window_start_list[j]))
    s.add(Implies(active[j], start_time[j] + min_duration_list[j] <= window_end_list[j]))
    s.add(Implies(active[j], start_time[j] >= 0))

opt.add(s.assertions())
opt.maximize(active_count)

if opt.check() == sat:
    m = opt.model()
    meeting_times = []
    for i in range(10):
        if is_true(m.eval(active[i])):
            start_val = m.eval(start_time[i])
            if isinstance(start_val, IntNumRef):
                start_minutes = start_val.as_long()
            else:
                start_minutes = int(str(start_val))
            duration = min_duration_list[i]
            end_minutes = start_minutes + duration
            start_hour = 9 + start_minutes // 60
            start_min = start_minutes % 60
            end_hour = 9 + end_minutes // 60
            end_min = end_minutes % 60
            start_str = f"{start_hour:02d}:{start_min:02d}"
            end_str = f"{end_hour:02d}:{end_min:02d}"
            meeting_times.append((start_minutes, names[i], start_str, end_str))
    meeting_times.sort(key=lambda x: x[0])
    itinerary = []
    for mt in meeting_times:
        itinerary.append({
            "action": "meet",
            "person": mt[1],
            "start_time": mt[2],
            "end_time": mt[3]
        })
    result = {"itinerary": itinerary}
    print(json.dumps(result))
else:
    print('{"itinerary": []}')