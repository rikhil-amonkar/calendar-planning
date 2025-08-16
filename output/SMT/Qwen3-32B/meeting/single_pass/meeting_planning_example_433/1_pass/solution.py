import z3
import json

# Define friends with their data
friends = [
    {
        'name': 'Deborah',
        'location': 'The Castro',
        'available_start': 825,  # 13:45
        'available_end': 1275,   # 21:15
        'duration': 90,
        'travel_time_from_Nob_Hill': 17,
    },
    {
        'name': 'Jeffrey',
        'location': 'Golden Gate Park',
        'available_start': 675,  # 11:15
        'available_end': 870,    # 14:30
        'duration': 120,
        'travel_time_from_Nob_Hill': 17,
    },
    {
        'name': 'Margaret',
        'location': 'Financial District',
        'available_start': 990,  # 16:30
        'available_end': 1215,   # 20:15
        'duration': 75,
        'travel_time_from_Nob_Hill': 9,
    },
    {
        'name': 'Emily',
        'location': 'Richmond District',
        'available_start': 1140, # 19:00
        'available_end': 1260,   # 21:00
        'duration': 15,
        'travel_time_from_Nob_Hill': 14,
    },
    {
        'name': 'Ronald',
        'location': 'North Beach',
        'available_start': 1110, # 18:30
        'available_end': 1170,   # 19:30
        'duration': 45,
        'travel_time_from_Nob_Hill': 8,
    }
]

# Define travel times between locations
travel_times = {
    ('Nob Hill', 'Richmond District'): 14,
    ('Nob Hill', 'Financial District'): 9,
    ('Nob Hill', 'North Beach'): 8,
    ('Nob Hill', 'The Castro'): 17,
    ('Nob Hill', 'Golden Gate Park'): 17,
    ('Richmond District', 'Nob Hill'): 17,
    ('Richmond District', 'Financial District'): 22,
    ('Richmond District', 'North Beach'): 17,
    ('Richmond District', 'The Castro'): 16,
    ('Richmond District', 'Golden Gate Park'): 9,
    ('Financial District', 'Nob Hill'): 8,
    ('Financial District', 'Richmond District'): 21,
    ('Financial District', 'North Beach'): 7,
    ('Financial District', 'The Castro'): 23,
    ('Financial District', 'Golden Gate Park'): 23,
    ('North Beach', 'Nob Hill'): 7,
    ('North Beach', 'Richmond District'): 18,
    ('North Beach', 'Financial District'): 8,
    ('North Beach', 'The Castro'): 22,
    ('North Beach', 'Golden Gate Park'): 22,
    ('The Castro', 'Nob Hill'): 16,
    ('The Castro', 'Richmond District'): 16,
    ('The Castro', 'Financial District'): 20,
    ('The Castro', 'North Beach'): 20,
    ('The Castro', 'Golden Gate Park'): 11,
    ('Golden Gate Park', 'Nob Hill'): 20,
    ('Golden Gate Park', 'Richmond District'): 7,
    ('Golden Gate Park', 'Financial District'): 26,
    ('Golden Gate Park', 'North Beach'): 24,
    ('Golden Gate Park', 'The Castro'): 13,
}

# Create Z3 solver
solver = z3.Optimize()

# Create variables for each friend
meet_vars = []
start_time_vars = []
end_time_vars = []
is_first_vars = []

for i, friend in enumerate(friends):
    meet = z3.Bool(f'meet_{i}')
    start_time = z3.Int(f'start_time_{i}')
    end_time = z3.Int(f'end_time_{i}')
    is_first = z3.Bool(f'is_first_{i}')
    meet_vars.append(meet)
    start_time_vars.append(start_time)
    end_time_vars.append(end_time)
    is_first_vars.append(is_first)

# Add constraints for each friend
for i, friend in enumerate(friends):
    meet = meet_vars[i]
    start_time = start_time_vars[i]
    end_time = end_time_vars[i]
    is_first = is_first_vars[i]
    available_start = friend['available_start']
    available_end = friend['available_end']
    duration = friend['duration']
    travel_time = friend['travel_time_from_Nob_Hill']

    # If meet is true, then start_time >= available_start
    solver.add(z3.Implies(meet, start_time >= available_start))
    # end_time = start_time + duration
    solver.add(z3.Implies(meet, end_time == start_time + duration))
    # end_time <= available_end
    solver.add(z3.Implies(meet, end_time <= available_end))
    # is_first implies meet
    solver.add(z3.Implies(is_first, meet))
    # is_first implies start_time >= base_time + travel_time
    base_time = 540  # 9:00 AM in minutes
    solver.add(z3.Implies(is_first, start_time >= base_time + travel_time))

# Add pairwise constraints for all pairs of friends
for i in range(len(friends)):
    for j in range(i+1, len(friends)):
        friend_i = friends[i]
        friend_j = friends[j]
        meet_i = meet_vars[i]
        meet_j = meet_vars[j]
        loc_i = friend_i['location']
        loc_j = friend_j['location']
        travel_time_i_to_j = travel_times[(loc_i, loc_j)]
        travel_time_j_to_i = travel_times[(loc_j, loc_i)]
        start_i = start_time_vars[i]
        duration_i = friend_i['duration']
        start_j = start_time_vars[j]
        duration_j = friend_j['duration']

        # If both meet_i and meet_j are true, then one of the two constraints must hold
        constraint = z3.Implies(
            z3.And(meet_i, meet_j),
            z3.Or(
                start_j >= start_i + duration_i + travel_time_i_to_j,
                start_i >= start_j + duration_j + travel_time_j_to_i
            )
        )
        solver.add(constraint)

# Add constraint that if any friend is met, exactly one is_first is true
sum_meet = z3.Sum([z3.If(m, 1, 0) for m in meet_vars])
sum_is_first = z3.Sum([z3.If(f, 1, 0) for f in is_first_vars])

# If sum_meet > 0, then sum_is_first == 1
solver.add(z3.Implies(sum_meet > 0, sum_is_first == 1))

# Maximize the number of friends met
solver.maximize(sum_meet)

# Check if the problem is satisfiable
result = solver.check()

if result == z3.sat:
    model = solver.model()
    # Extract which friends are met
    met_friends = []
    for i, friend in enumerate(friends):
        if model.evaluate(meet_vars[i]):
            met_friends.append(i)
    
    # Sort met friends by start time
    met_friends_sorted = sorted(met_friends, key=lambda x: model.evaluate(start_time_vars[x]).as_long())
    
    # Build itinerary
    itinerary = []
    for idx in met_friends_sorted:
        friend = friends[idx]
        start = model.evaluate(start_time_vars[idx]).as_long()
        end = model.evaluate(end_time_vars[idx]).as_long()
        # Convert to HH:MM format
        start_hours = start // 60
        start_minutes = start % 60
        end_hours = end // 60
        end_minutes = end % 60
        start_time_str = f"{start_hours:02d}:{start_minutes:02d}"
        end_time_str = f"{end_hours:02d}:{end_minutes:02d}"
        itinerary.append({
            "action": "meet",
            "person": friend['name'],
            "start_time": start_time_str,
            "end_time": end_time_str
        })
    
    print("SOLUTION:")
    print(json.dumps({"itinerary": itinerary}))
else:
    print("No solution found.")