from z3 import *
import json

# Define travel times (same as before)
travel_times = {
    # ... (same travel_times dictionary as before)
}

# Define friends' availability (same as before)
friends = [
    # ... (same friends list as before)
]

# Initialize solver with optimization
opt = Optimize()

# Create meeting variables
meetings = {}
for friend in friends:
    name = friend['name']
    meetings[name] = {
        'start': Int(f'start_{name}'),
        'end': Int(f'end_{name}'),
        'location': friend['location'],
        'duration': friend['duration'],
        'available_start': friend['start'][0] * 60 + friend['start'][1],
        'available_end': friend['end'][0] * 60 + friend['end'][1],
        'met': Bool(f'met_{name}')
    }

# Basic meeting constraints
for name, m in meetings.items():
    opt.add(Implies(m['met'], m['start'] >= m['available_start']))
    opt.add(Implies(m['met'], m['end'] <= m['available_end']))
    opt.add(Implies(m['met'], m['end'] == m['start'] + m['duration']))

# Create meeting order variables
meeting_names = [f['name'] for f in friends]
order = [[Bool(f'order_{i}_{j}') for j in range(len(meeting_names))] 
          for i in range(len(meeting_names))]

# Order constraints
for i in range(len(meeting_names)):
    for j in range(len(meeting_names)):
        if i == j:
            opt.add(order[i][j] == False)
        else:
            opt.add(Implies(order[i][j], Not(order[j][i]))

# Travel time constraints
for i in range(len(meeting_names)):
    for j in range(len(meeting_names)):
        if i != j:
            m1 = meeting_names[i]
            m2 = meeting_names[j]
            loc1 = meetings[m1]['location']
            loc2 = meetings[m2]['location']
            travel = travel_times.get(loc1, {}).get(loc2, 0)
            
            # If both meetings happen and m1 is before m2
            opt.add(Implies(And(meetings[m1]['met'], meetings[m2]['met'], order[i][j]),
                          meetings[m2]['start'] >= meetings[m1]['end'] + travel))

# First meeting constraint
first_meeting = [Bool(f'first_{name}') for name in meeting_names]
opt.add(Sum([If(f, 1, 0) for f in first_meeting]) == 1)  # Exactly one first meeting

for i, name in enumerate(meeting_names):
    travel = travel_times['Pacific Heights'][meetings[name]['location']]
    opt.add(Implies(first_meeting[i],
                   And(meetings[name]['met'],
                       meetings[name]['start'] >= 540 + travel)))
    
    # First meeting must be before all others
    for j in range(len(meeting_names)):
        if i != j:
            opt.add(Implies(first_meeting[i], order[i][j]))

# Maximize number of meetings
opt.maximize(Sum([If(m['met'], 1, 0) for m in meetings.values()]))

# Find solution
if opt.check() == sat:
    model = opt.model()
    itinerary = []
    for name, m in meetings.items():
        if model.evaluate(m['met']):
            start = model.evaluate(m['start']).as_long()
            end = model.evaluate(m['end']).as_long()
            itinerary.append({
                'action': 'meet',
                'person': name,
                'start_time': f"{start//60:02d}:{start%60:02d}",
                'end_time': f"{end//60:02d}:{end%60:02d}"
            })
    itinerary.sort(key=lambda x: x['start_time'])
    print(json.dumps({'itinerary': itinerary}, indent=2))
else:
    print('No feasible schedule found.')