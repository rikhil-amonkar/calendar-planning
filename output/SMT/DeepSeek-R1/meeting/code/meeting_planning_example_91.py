from z3 import *

# Define travel times between locations
travel_time = {
    'Russian Hill': {
        'Richmond District': 14,
    },
    'Richmond District': {
        'Russian Hill': 13,
    }
}

# Friend data: (name, location, available_start, available_end, required_duration)
friends_data = [
    ('Daniel', 'Richmond District', 1140, 1215, 75),
]

# Initialize Z3 solver
s = Optimize()

# Create variables for friend
friends = []
for name, loc, start_t, end_t, dur in friends_data:
    visited = Bool(f'visited_{name}')
    start = Int(f'start_{name}')
    end = Int(f'end_{name}')
    friends.append({
        'name': name,
        'location': loc,
        'start_t': start_t,
        'end_t': end_t,
        'dur': dur,
        'visited': visited,
        'start': start,
        'end': end,
    })

# Add constraints for the friend
for f in friends:
    # If visited, ensure time within availability and duration
    s.add(Implies(f['visited'], And(f['start'] >= f['start_t'], f['end'] <= f['end_t'])))
    s.add(Implies(f['visited'], f['end'] - f['start'] >= f['dur']))

# Initial constraint: Start at Russian Hill at 9:00AM (540 minutes)
for f in friends:
    loc = f['location']
    travel = travel_time['Russian Hill'][loc]
    s.add(Implies(f['visited'], f['start'] >= 540 + travel))  # Arrival after travel time

# Maximize number of friends met (only Daniel in this case)
sum_visited = Sum([If(f['visited'], 1, 0) for f in friends])
s.maximize(sum_visited)

# Solve and display results
if s.check() == sat:
    model = s.model()
    print("Optimal schedule:")
    schedule = []
    for f in friends:
        if model.evaluate(f['visited']):
            start_val = model.evaluate(f['start']).as_long()
            end_val = model.evaluate(f['end']).as_long()
            schedule.append((start_val, end_val, f['name']))
    # Sort by start time
    schedule.sort()
    for sched in schedule:
        start_hr = sched[0] // 60
        start_min = sched[0] % 60
        end_hr = sched[1] // 60
        end_min = sched[1] % 60
        print(f"{sched[2]}: {start_hr:02}:{start_min:02} - {end_hr:02}:{end_min:02}")
else:
    print("No solution found")