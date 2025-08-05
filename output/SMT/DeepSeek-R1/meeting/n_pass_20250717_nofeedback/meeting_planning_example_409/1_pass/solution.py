from z3 import *
import json

# Define meetings with their constraints
meetings = [
    {'name': 'Thomas', 'loc': 'BV', 'duration': 120, 'start_min': 930, 'end_min': 1110},
    {'name': 'Stephanie', 'loc': 'GG', 'duration': 30, 'start_min': 1110, 'end_min': 1305},
    {'name': 'Laura', 'loc': 'NH', 'duration': 30, 'start_min': 540, 'end_min': 975},
    {'name': 'Betty', 'loc': 'MD', 'duration': 45, 'start_min': 1125, 'end_min': 1305},
    {'name': 'Patricia', 'loc': 'EM', 'duration': 45, 'start_min': 1050, 'end_min': 1320}
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

# Create Z3 variables
order = IntVector('order', 5)
st = IntVector('st', 5)

s = Solver()

# Constraints for order: each element in [0,4] and distinct
for i in range(5):
    s.add(order[i] >= 0, order[i] < 5)
s.add(Distinct(order))

# First meeting constraint: start time >= 540 + travel time from FW
first_idx = order[0]
s.add(st[first_idx] >= 540 + travel_time_dict[('FW', meetings[first_idx]['loc']])

# Window constraints for each meeting
for i in range(5):
    mtg = meetings[i]
    s.add(st[i] >= mtg['start_min'])
    s.add(st[i] + mtg['duration'] <= mtg['end_min'])

# Travel time constraints between consecutive meetings
for k in range(4):
    i1 = order[k]
    i2 = order[k+1]
    loc1 = meetings[i1]['loc']
    loc2 = meetings[i2]['loc']
    travel_dur = travel_time_dict.get((loc1, loc2))
    if travel_dur is None:
        travel_dur = 0  # Should not happen, but safe guard
    s.add(st[i2] >= st[i1] + meetings[i1]['duration'] + travel_dur)

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
    # Fallback if no solution for 5 meetings (though one exists)
    print("SOLUTION:")
    print('{"itinerary": []}')