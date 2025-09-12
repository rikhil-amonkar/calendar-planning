import z3
import json

friends_data = {
    'Karen': {
        'location': 'Russian Hill',
        'available_start': 20 * 60 + 45,  # 8:45 PM
        'available_end': 21 * 60 + 45,    # 9:45 PM
        'required_duration': 60,
    },
    'Jessica': {
        'location': 'The Castro',
        'available_start': 15 * 60 + 45,  # 3:45 PM
        'available_end': 19 * 60 + 30,    # 7:30 PM
        'required_duration': 60,
    },
    'Matthew': {
        'location': 'Richmond District',
        'available_start': 7 * 60 + 30,   # 7:30 AM
        'available_end': 15 * 60 + 15,    # 3:15 PM
        'required_duration': 15,
    },
    'Michelle': {
        'location': 'Marina District',
        'available_start': 10 * 60 + 30,  # 10:30 AM
        'available_end': 18 * 60 + 45,    # 6:45 PM
        'required_duration': 75,
    },
    'Carol': {
        'location': 'North Beach',
        'available_start': 12 * 60 + 0,   # 12:00 PM
        'available_end': 17 * 60 + 0,     # 5:00 PM
        'required_duration': 90,
    },
    'Stephanie': {
        'location': 'Union Square',
        'available_start': 10 * 60 + 45,  # 10:45 AM
        'available_end': 14 * 60 + 15,    # 2:15 PM
        'required_duration': 30,
    },
    'Linda': {
        'location': 'Golden Gate Park',
        'available_start': 10 * 60 + 45,  # 10:45 AM
        'available_end': 22 * 60 + 0,     # 10:00 PM
        'required_duration': 90,
    },
}

travel_times = {
    'Sunset District': {
        'Russian Hill': 24,
        'The Castro': 17,
        'Richmond District': 12,
        'Marina District': 21,
        'North Beach': 29,
        'Union Square': 30,
        'Golden Gate Park': 11,
    },
    'Russian Hill': {
        'Sunset District': 23,
        'The Castro': 21,
        'Richmond District': 14,
        'Marina District': 7,
        'North Beach': 5,
        'Union Square': 11,
        'Golden Gate Park': 21,
    },
    'The Castro': {
        'Sunset District': 17,
        'Russian Hill': 18,
        'Richmond District': 16,
        'Marina District': 21,
        'North Beach': 20,
        'Union Square': 19,
        'Golden Gate Park': 11,
    },
    'Richmond District': {
        'Sunset District': 11,
        'Russian Hill': 13,
        'The Castro': 16,
        'Marina District': 9,
        'North Beach': 17,
        'Union Square': 21,
        'Golden Gate Park': 9,
    },
    'Marina District': {
        'Sunset District': 19,
        'Russian Hill': 8,
        'The Castro': 22,
        'Richmond District': 11,
        'North Beach': 11,
        'Union Square': 16,
        'Golden Gate Park': 18,
    },
    'North Beach': {
        'Sunset District': 27,
        'Russian Hill': 4,
        'The Castro': 22,
        'Richmond District': 18,
        'Marina District': 9,
        'Union Square': 7,
        'Golden Gate Park': 22,
    },
    'Union Square': {
        'Sunset District': 26,
        'Russian Hill': 13,
        'The Castro': 19,
        'Richmond District': 20,
        'Marina District': 18,
        'North Beach': 10,
        'Golden Gate Park': 22,
    },
    'Golden Gate Park': {
        'Sunset District': 10,
        'Russian Hill': 19,
        'The Castro': 13,
        'Richmond District': 7,
        'Marina District': 16,
        'North Beach': 24,
        'Union Square': 22,
    },
}

friends = list(friends_data.keys())

s = z3.Optimize()

included = {f: s.Bool(f'included_{f}') for f in friends}
pos = {f: s.Int(f'pos_{f}') for f in friends}
start_time = {f: s.Int(f'start_{f}') for f in friends}
end_time = {f: s.Int(f'end_{f}') for f in friends}
arrival_time = {f: s.Int(f'arrival_{f}') for f in friends}

# Constraints for each friend
for f in friends:
    # Position must be between 0 and 6 if included
    s.add(z3.Implies(included[f], z3.And(pos[f] >= 0, pos[f] <= 6)))
    
    # If included and position is 0, arrival time is initial time + travel from Sunset
    loc_f = friends_data[f]['location']
    initial_time = 9 * 60  # 9:00 AM
    s.add(z3.Implies(z3.And(included[f], pos[f] == 0), 
                     arrival_time[f] == initial_time + travel_times['Sunset District'][loc_f]))
    
    # For each other friend g, if pos[g] == pos[f] -1, then arrival time is based on g's end time
    for g in friends:
        if f != g:
            loc_g = friends_data[g]['location']
            loc_f = friends_data[f]['location']
            travel = travel_times[loc_g][loc_f]
            s.add(z3.Implies(
                z3.And(included[f], included[g], pos[g] == pos[f] - 1),
                arrival_time[f] == end_time[g] + travel
            ))
    
    # Start time constraints
    available_start = friends_data[f]['available_start']
    required_duration = friends_data[f]['required_duration']
    available_end = friends_data[f]['available_end']
    s.add(z3.Implies(included[f], z3.And(
        start_time[f] >= arrival_time[f],
        start_time[f] >= available_start,
        end_time[f] == start_time[f] + required_duration,
        end_time[f] <= available_end
    )))

# Ensure that for each included friend with pos > 0, there exists a predecessor
for f in friends:
    for k in range(1, 7):  # since pos can be up to 6
        cond = z3.And(included[f], pos[f] == k)
        # Check if there exists a friend g with pos == k-1 and included
        exists_prev = z3.Or([z3.And(included[g], pos[g] == k-1) for g in friends])
        s.add(z3.Implies(cond, exists_prev))

# Uniqueness of positions for included friends
for f in friends:
    for g in friends:
        if f != g:
            s.add(z3.Implies(z3.And(included[f], included[g]), pos[f] != pos[g]))

# Maximize the number of included friends
sum_included = z3.Sum([z3.If(included[f], 1, 0) for f in friends])
s.maximize(sum_included)

# Solve
if s.check() == z3.sat:
    model = s.model()
    # Extract included friends
    included_friends = [f for f in friends if model.evaluate(included[f])]
    # Sort by position
    included_friends_sorted = sorted(included_friends, key=lambda f: model.evaluate(pos[f]).as_long())
    
    # Prepare the itinerary
    itinerary = []
    for f in included_friends_sorted:
        start = model.evaluate(start_time[f]).as_long()
        end = model.evaluate(end_time[f]).as_long()
        # Convert to H:MM format
        def to_time(m):
            h = m // 60
            mi = m % 60
            return f"{h}:{mi:02d}"
        itinerary.append({
            "action": "meet",
            "location": friends_data[f]['location'],
            "person": f,
            "start_time": to_time(start),
            "end_time": to_time(end)
        })
    
    # Output JSON
    print(json.dumps({"itinerary": itinerary}))
else:
    print("No solution found.")