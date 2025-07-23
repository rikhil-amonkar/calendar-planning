from z3 import *
import json

# Define meetings with their constraints
meetings = [
    {'name': 'Thomas', 'loc': 'BV', 'duration': 120, 'start_min': 930, 'end_min': 1110},   # 3:30PM to 6:30PM
    {'name': 'Stephanie', 'loc': 'GG', 'duration': 30, 'start_min': 1110, 'end_min': 1305}, # 6:30PM to 9:45PM
    {'name': 'Laura', 'loc': 'NH', 'duration': 30, 'start_min': 525, 'end_min': 975},       # 8:45AM to 4:15PM
    {'name': 'Betty', 'loc': 'MD', 'duration': 45, 'start_min': 1125, 'end_min': 1305},     # 6:45PM to 9:45PM
    {'name': 'Patricia', 'loc': 'EM', 'duration': 45, 'start_min': 1050, 'end_min': 1320}   # 5:30PM to 10:00PM
]

# Travel time dictionary
travel_time_dict = {
    ('FW', 'BV'): 26, ('FW', 'GG'): 25, ('FW', 'NH'): 11, ('FW', 'MD'): 9, ('FW', 'EM'): 8,
    ('BV', 'FW'): 25, ('BV', 'GG'): 22, ('BV', 'NH'): 20, ('BV', 'MD'): 25, ('BV', 'EM'): 19,
    ('GG', 'FW'): 24, ('GG', 'BV'): 23, ('GG', 'NH'): 20, ('GG', 'MD'): 16, ('GG', 'EM'): 25,
    ('NH', 'FW'): 11, ('NH', 'BV'): 19, ('NH', 'GG'): 17, ('NH', 'MD'): 11, ('NH', 'EM'): 9,
    ('MD', 'FW'): 10, ('MD', 'BV'): 27, ('MD', 'GG'): 18, ('MD', 'NH'): 12, ('MD', 'EM'): 14,
    ('EM', 'FW'): 6, ('EM', 'BV'): 21, ('EM', 'GG'): 25, ('EM', 'NH'): 10, ('EM', 'MD'): 12
}

# Precompute initial travel times from FW to each meeting location
initial_travel_time = []
for mtg in meetings:
    key = ('FW', mtg['loc'])
    initial_travel_time.append(travel_time_dict[key])

# Precompute travel matrix between meetings: 5x5
travel_matrix = []
for i in range(5):
    row = []
    for j in range(5):
        loc_i = meetings[i]['loc']
        loc_j = meetings[j]['loc']
        key = (loc_i, loc_j)
        row.append(travel_time_dict[key])
    travel_matrix.append(row)

# Create Z3 variables
order = IntVector('order', 5)
st = IntVector('st', 5)

s = Solver()

# Order constraints: each between 0 and 4, distinct
for i in range(5):
    s.add(order[i] >= 0, order[i] < 5)
s.add(Distinct(order))

# First meeting constraint: if meeting i is first, then its start time >= 540 + initial_travel_time[i]
for i in range(5):
    s.add(If(order[0] == i, st[i] >= 540 + initial_travel_time[i], True))

# Consecutive meetings
for k in range(4):  # k from 0 to 3
    for i in range(5):
        for j in range(5):
            s.add(If(And(order[k] == i, order[k+1] == j),
                     st[j] >= st[i] + meetings[i]['duration'] + travel_matrix[i][j],
                     True))

# Window constraints for each meeting
for i in range(5):
    mtg = meetings[i]
    s.add(st[i] >= mtg['start_min'])
    s.add(st[i] + mtg['duration'] <= mtg['end_min'])

# Check for a solution
if s.check() == sat:
    m = s.model()
    start_times = [m[st[i]].as_long() for i in range(5)]
    events = []
    for i in range(5):
        start_val = start_times[i]
        end_val = start_val + meetings[i]['duration']
        events.append({
            'name': meetings[i]['name'],
            'start': start_val,
            'end': end_val
        })
    # Sort events by start time
    events_sorted = sorted(events, key=lambda x: x['start'])
    itinerary = []
    for event in events_sorted:
        # Convert minutes to HH:MM
        start_min = event['start']
        start_hour = start_min // 60
        start_minute = start_min % 60
        end_min = event['end']
        end_hour = end_min // 60
        end_minute = end_min % 60
        start_str = f"{start_hour:02d}:{start_minute:02d}"
        end_str = f"{end_hour:02d}:{end_minute:02d}"
        itinerary.append({
            "action": "meet",
            "person": event['name'],
            "start_time": start_str,
            "end_time": end_str
        })
    output = {"itinerary": itinerary}
    print("SOLUTION:")
    print(json.dumps(output))
else:
    # Fallback if no solution found
    print("SOLUTION:")
    print('{"itinerary": []}')