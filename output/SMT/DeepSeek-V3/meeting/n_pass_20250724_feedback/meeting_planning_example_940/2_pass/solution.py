from z3 import *
import json

def time_to_minutes(time_str):
    hh, mm = map(int, time_str.split(':'))
    return hh * 60 + mm - 540  # 9:00 AM is 540 minutes

def minutes_to_time(minutes):
    total_minutes = 540 + minutes
    hh = total_minutes // 60
    mm = total_minutes % 60
    return f"{hh:02d}:{mm:02d}"

# Initialize solver
s = Optimize()

# Travel times (simplified to only include necessary routes)
travel_times = {
    ('Union Square', 'Russian Hill'): 13,
    ('Russian Hill', 'Nob Hill'): 5,
    ('Nob Hill', 'Union Square'): 7,
    ('Union Square', 'North Beach'): 10,
    ('North Beach', 'Chinatown'): 6,
    ('Chinatown', 'Pacific Heights'): 10,
    ('Pacific Heights', 'Marina District'): 6,
    ('Marina District', 'Fisherman\'s Wharf'): 10,
    ('Fisherman\'s Wharf', 'The Castro'): 27,
    ('The Castro', 'Mission District'): 7,
    ('Mission District', 'Sunset District'): 24,
    ('Sunset District', 'Union Square'): 30,
}

friends = {
    'Kevin': {'location': 'Mission District', 'start': '20:45', 'end': '21:45', 'min_duration': 60},
    'Mark': {'location': 'Fisherman\'s Wharf', 'start': '17:15', 'end': '20:00', 'min_duration': 90},
    'Jessica': {'location': 'Russian Hill', 'start': '09:00', 'end': '15:00', 'min_duration': 120},
    'Jason': {'location': 'Marina District', 'start': '15:15', 'end': '21:45', 'min_duration': 120},
    'John': {'location': 'North Beach', 'start': '09:45', 'end': '18:00', 'min_duration': 15},
    'Karen': {'location': 'Chinatown', 'start': '16:45', 'end': '19:00', 'min_duration': 75},
    'Sarah': {'location': 'Pacific Heights', 'start': '17:30', 'end': '18:15', 'min_duration': 45},
    'Amanda': {'location': 'The Castro', 'start': '20:00', 'end': '21:15', 'min_duration': 60},
    'Nancy': {'location': 'Nob Hill', 'start': '09:45', 'end': '13:00', 'min_duration': 45},
    'Rebecca': {'location': 'Sunset District', 'start': '08:45', 'end': '15:00', 'min_duration': 75},
}

# Create variables
meetings = {}
for name in friends:
    start = Int(f'start_{name}')
    end = Int(f'end_{name}')
    meetings[name] = {'start': start, 'end': end, 'met': Bool(f'met_{name}')}

# Basic constraints
for name in friends:
    friend = friends[name]
    start_min = time_to_minutes(friend['start'])
    end_min = time_to_minutes(friend['end'])
    min_duration = friend['min_duration']
    
    s.add(Implies(meetings[name]['met'], meetings[name]['start'] >= start_min))
    s.add(Implies(meetings[name]['met'], meetings[name]['end'] <= end_min))
    s.add(Implies(meetings[name]['met'], meetings[name]['end'] - meetings[name]['start'] >= min_duration))

# Initial location and time
current_location = 'Union Square'
current_time = 0

# Define meeting order (heuristic)
meeting_order = ['Jessica', 'Nancy', 'John', 'Karen', 'Sarah', 'Jason', 'Mark', 'Amanda', 'Kevin', 'Rebecca']

# Travel constraints
for i in range(len(meeting_order)-1):
    name1 = meeting_order[i]
    name2 = meeting_order[i+1]
    loc1 = friends[name1]['location']
    loc2 = friends[name2]['location']
    
    travel = travel_times.get((loc1, loc2), 999)  # Large number if no direct route
    
    s.add(Implies(And(meetings[name1]['met'], meetings[name2]['met']),
              meetings[name2]['start'] >= meetings[name1]['end'] + travel))

# No overlapping meetings
for name1 in meetings:
    for name2 in meetings:
        if name1 != name2:
            s.add(Or(
                Not(meetings[name1]['met']),
                Not(meetings[name2]['met']),
                meetings[name1]['end'] <= meetings[name2]['start'],
                meetings[name2]['end'] <= meetings[name1]['start']
            ))

# Maximize number of meetings
s.maximize(Sum([If(meetings[name]['met'], 1, 0) for name in meetings]))

# Check and get model
if s.check() == sat:
    m = s.model()
    itinerary = []
    for name in meeting_order:
        if is_true(m[meetings[name]['met']]):
            start = m[meetings[name]['start']].as_long()
            end = m[meetings[name]['end']].as_long()
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": minutes_to_time(start),
                "end_time": minutes_to_time(end)
            })
    print("SOLUTION:")
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found")