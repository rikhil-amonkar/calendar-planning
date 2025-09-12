from z3 import *
import json

# Define travel times between locations
travel_time = {
    # From Embarcadero
    ('Embarcadero', 'Golden Gate Park'): 25,
    ('Embarcadero', 'Haight-Ashbury'): 21,
    ('Embarcadero', 'Bayview'): 21,
    ('Embarcadero', 'Presidio'): 20,
    ('Embarcadero', 'Financial District'): 5,
    # From Golden Gate Park
    ('Golden Gate Park', 'Embarcadero'): 25,
    ('Golden Gate Park', 'Haight-Ashbury'): 7,
    ('Golden Gate Park', 'Bayview'): 23,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'Financial District'): 26,
    # From Haight-Ashbury
    ('Haight-Ashbury', 'Embarcadero'): 20,
    ('Haight-Ashbury', 'Golden Gate Park'): 7,
    ('Haight-Ashbury', 'Bayview'): 18,
    ('Haight-Ashbury', 'Presidio'): 15,
    ('Haight-Ashbury', 'Financial District'): 21,
    # From Bayview
    ('Bayview', 'Embarcadero'): 19,
    ('Bayview', 'Golden Gate Park'): 22,
    ('Bayview', 'Haight-Ashbury'): 19,
    ('Bayview', 'Presidio'): 31,
    ('Bayview', 'Financial District'): 19,
    # From Presidio
    ('Presidio', 'Embarcadero'): 20,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Haight-Ashbury'): 15,
    ('Presidio', 'Bayview'): 31,
    ('Presidio', 'Financial District'): 23,
    # From Financial District
    ('Financial District', 'Embarcadero'): 4,
    ('Financial District', 'Golden Gate Park'): 23,
    ('Financial District', 'Haight-Ashbury'): 19,
    ('Financial District', 'Bayview'): 19,
    ('Financial District', 'Presidio'): 22,
}

# Define friend data (name, location, available times, min duration)
friends_data = [
    {
        'name': 'Mary',
        'location': 'Golden Gate Park',
        'available_start': 525,  # 8:45 AM
        'available_end': 705,    # 11:45 AM
        'min_duration': 45
    },
    {
        'name': 'Kevin',
        'location': 'Haight-Ashbury',
        'available_start': 615,  # 10:15 AM
        'available_end': 975,    # 4:15 PM
        'min_duration': 90
    },
    {
        'name': 'Deborah',
        'location': 'Bayview',
        'available_start': 900,  # 3:00 PM
        'available_end': 1155,   # 7:15 PM
        'min_duration': 120
    },
    {
        'name': 'Stephanie',
        'location': 'Presidio',
        'available_start': 600,  # 10:00 AM
        'available_end': 1035,   # 5:15 PM
        'min_duration': 120
    },
    {
        'name': 'Emily',
        'location': 'Financial District',
        'available_start': 690,  # 11:30 AM
        'available_end': 1305,   # 9:45 PM
        'min_duration': 105
    }
]

friends = ['Mary', 'Kevin', 'Deborah', 'Stephanie', 'Emily']

# Initialize Z3 solver
solver = Optimize()

# Create variables for meeting decisions and time constraints
meet_vars = {}
start_vars = {}
end_vars = {}

for friend in friends:
    meet = Bool(f'meet_{friend}')
    meet_vars[friend] = meet
    start = Int(f'start_{friend}')
    end = Int(f'end_{friend}')
    start_vars[friend] = start
    end_vars[friend] = end
    solver.add(Implies(meet, end >= start))  # Ensure end >= start

initial_time = 540  # 9:00 AM in minutes

for friend in friends:
    data = next(f for f in friends_data if f['name'] == friend)
    loc = data['location']
    available_start = data['available_start']
    available_end = data['available_end']
    min_duration = data['min_duration']
    travel_time_from_emb = travel_time[('Embarcadero', loc)]
    meet = meet_vars[friend]
    start = start_vars[friend]
    end = end_vars[friend]
    
    # Add constraints if the friend is met
    solver.add(Implies(meet, start >= initial_time + travel_time_from_emb))
    solver.add(Implies(meet, start >= available_start))
    solver.add(Implies(meet, end <= available_end))
    solver.add(Implies(meet, end - start >= min_duration))

# Add pairwise constraints between friends
for i in range(len(friends)):
    for j in range(i + 1, len(friends)):
        friend1 = friends[i]
        friend2 = friends[j]
        meet1 = meet_vars[friend1]
        meet2 = meet_vars[friend2]
        start1 = start_vars[friend1]
        end1 = end_vars[friend1]
        loc1 = next(f for f in friends_data if f['name'] == friend1)['location']
        start2 = start_vars[friend2]
        end2 = end_vars[friend2]
        loc2 = next(f for f in friends_data if f['name'] == friend2)['location']
        travel1to2 = travel_time[(loc1, loc2)]
        travel2to1 = travel_time[(loc2, loc1)]
        solver.add(Implies(And(meet1, meet2), Or(
            start2 >= end1 + travel1to2,
            start1 >= end2 + travel2to1
        )))

# Objective: Maximize the number of friends met
objective = Sum([If(meet_vars[friend], 1, 0) for friend in friends])
solver.maximize(objective)

# Solve and output the result
if solver.check() == sat:
    model = solver.model()
    met_friends = []
    for friend in friends:
        if is_true(model.evaluate(meet_vars[friend])):
            data = next(f for f in friends_data if f['name'] == friend)
            start_val = model.evaluate(start_vars[friend]).as_long()
            end_val = model.evaluate(end_vars[friend]).as_long()
            met_friends.append({
                'name': friend,
                'location': data['location'],
                'start': start_val,
                'end': end_val
            })
    # Sort by start time to determine meeting order
    met_friends.sort(key=lambda x: x['start'])
    # Format the result as JSON
    itinerary = []
    for f in met_friends:
        def to_time_str(m):
            hours = m // 60
            minutes = m % 60
            return f"{hours}:{minutes:02d}"
        itinerary.append({
            "action": "meet",
            "location": f['location'],
            "person": f['name'],
            "start_time": to_time_str(f['start']),
            "end_time": to_time_str(f['end'])
        })
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found.")