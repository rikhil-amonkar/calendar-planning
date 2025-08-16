import z3
import json

# Define travel times between locations
travel_time_dict = {
    'Union Square': {
        'Presidio': 24,
        'Alamo Square': 15,
        'Marina District': 18,
        'Financial District': 9,
        'Nob Hill': 9,
        'Sunset District': 27,
        'Chinatown': 7,
        'Russian Hill': 13,
        'North Beach': 10,
        'Haight-Ashbury': 18,
    },
    'Presidio': {
        'Union Square': 22,
        'Alamo Square': 19,
        'Marina District': 11,
        'Financial District': 23,
        'Nob Hill': 18,
        'Sunset District': 15,
        'Chinatown': 21,
        'Russian Hill': 14,
        'North Beach': 18,
        'Haight-Ashbury': 15,
    },
    'Alamo Square': {
        'Union Square': 14,
        'Presidio': 17,
        'Marina District': 15,
        'Financial District': 17,
        'Nob Hill': 11,
        'Sunset District': 16,
        'Chinatown': 15,
        'Russian Hill': 13,
        'North Beach': 15,
        'Haight-Ashbury': 5,
    },
    'Marina District': {
        'Union Square': 16,
        'Presidio': 10,
        'Alamo Square': 15,
        'Financial District': 17,
        'Nob Hill': 12,
        'Sunset District': 19,
        'Chinatown': 15,
        'Russian Hill': 8,
        'North Beach': 11,
        'Haight-Ashbury': 16,
    },
    'Financial District': {
        'Union Square': 9,
        'Presidio': 22,
        'Alamo Square': 17,
        'Marina District': 15,
        'Nob Hill': 8,
        'Sunset District': 30,
        'Chinatown': 5,
        'Russian Hill': 11,
        'North Beach': 7,
        'Haight-Ashbury': 19,
    },
    'Nob Hill': {
        'Union Square': 7,
        'Presidio': 17,
        'Alamo Square': 11,
        'Marina District': 11,
        'Financial District': 9,
        'Sunset District': 24,
        'Chinatown': 6,
        'Russian Hill': 5,
        'North Beach': 8,
        'Haight-Ashbury': 13,
    },
    'Sunset District': {
        'Union Square': 30,
        'Presidio': 16,
        'Alamo Square': 17,
        'Marina District': 21,
        'Financial District': 30,
        'Nob Hill': 27,
        'Chinatown': 30,
        'Russian Hill': 24,
        'North Beach': 28,
        'Haight-Ashbury': 15,
    },
    'Chinatown': {
        'Union Square': 7,
        'Presidio': 19,
        'Alamo Square': 17,
        'Marina District': 12,
        'Financial District': 5,
        'Nob Hill': 9,
        'Sunset District': 30,
        'Russian Hill': 7,
        'North Beach': 3,
        'Haight-Ashbury': 19,
    },
    'Russian Hill': {
        'Union Square': 10,
        'Presidio': 14,
        'Alamo Square': 15,
        'Marina District': 7,
        'Financial District': 11,
        'Nob Hill': 5,
        'Sunset District': 23,
        'Chinatown': 9,
        'North Beach': 5,
        'Haight-Ashbury': 17,
    },
    'North Beach': {
        'Union Square': 7,
        'Presidio': 17,
        'Alamo Square': 16,
        'Marina District': 9,
        'Financial District': 8,
        'Nob Hill': 7,
        'Sunset District': 27,
        'Chinatown': 6,
        'Russian Hill': 4,
        'Haight-Ashbury': 18,
    },
    'Haight-Ashbury': {
        'Union Square': 19,
        'Presidio': 15,
        'Alamo Square': 5,
        'Marina District': 17,
        'Financial District': 21,
        'Nob Hill': 15,
        'Sunset District': 15,
        'Chinatown': 19,
        'Russian Hill': 17,
        'North Beach': 19,
    },
}

friends_data = [
    {
        'id': 1,
        'name': 'Kimberly',
        'available_start': 15 * 60 + 30,  # 15:30
        'available_end': 16 * 60,         # 16:00
        'duration': 15,
        'location': 'Presidio'
    },
    {
        'id': 2,
        'name': 'Elizabeth',
        'available_start': 19 * 60 + 15,  # 19:15
        'available_end': 20 * 60 + 15,    # 20:15
        'duration': 15,
        'location': 'Alamo Square'
    },
    {
        'id': 3,
        'name': 'Joshua',
        'available_start': 10 * 60 + 30,  # 10:30 AM
        'available_end': 14 * 60 + 15,    # 14:15 PM
        'duration': 45,
        'location': 'Marina District'
    },
    {
        'id': 4,
        'name': 'Sandra',
        'available_start': 18 * 60 + 30,  # 18:30
        'available_end': 20 * 60 + 15,    # 20:15
        'duration': 45,
        'location': 'Financial District'
    },
    {
        'id': 5,
        'name': 'Kenneth',
        'available_start': 12 * 60 + 45,  # 12:45 PM
        'available_end': 21 * 60 + 45,    # 21:45 PM
        'duration': 30,
        'location': 'Nob Hill'
    },
    {
        'id': 6,
        'name': 'Betty',
        'available_start': 14 * 60,       # 14:00
        'available_end': 19 * 60,         # 19:00
        'duration': 60,
        'location': 'Sunset District'
    },
    {
        'id': 7,
        'name': 'Deborah',
        'available_start': 17 * 60 + 15,  # 17:15
        'available_end': 20 * 60 + 30,    # 20:30
        'duration': 15,
        'location': 'Chinatown'
    },
    {
        'id': 8,
        'name': 'Barbara',
        'available_start': 17 * 60 + 30,  # 17:30
        'available_end': 21 * 60 + 15,    # 21:15
        'duration': 120,
        'location': 'Russian Hill'
    },
    {
        'id': 9,
        'name': 'Steven',
        'available_start': 17 * 60 + 45,  # 17:45
        'available_end': 20 * 60 + 45,    # 20:45
        'duration': 90,
        'location': 'North Beach'
    },
    {
        'id': 10,
        'name': 'Daniel',
        'available_start': 18 * 60 + 30,  # 18:30
        'available_end': 18 * 60 + 45,    # 18:45
        'duration': 15,
        'location': 'Haight-Ashbury'
    },
]

friends_locations = {f['id']: f['location'] for f in friends_data}

MAX_STEPS = 10

friends = [z3.Int('friend_{}'.format(i)) for i in range(MAX_STEPS)]
start_times = [z3.Int('start_time_{}'.format(i)) for i in range(MAX_STEPS)]
end_times = [z3.Int('end_time_{}'.format(i)) for i in range(MAX_STEPS)]

solver = z3.Solver()

# Constraints for each step
for i in range(MAX_STEPS):
    solver.add(friends[i] >= 0)
    solver.add(friends[i] <= 10)

    for f in friends_data:
        fid = f['id']
        loc = f['location']
        as_ = f['available_start']
        ae_ = f['available_end']
        dur = f['duration']

        # If friend_i == fid, then add constraints
        cond = z3.If(friends[i] == fid,
                     z3.And(
                         start_times[i] >= 0,
                         end_times[i] == start_times[i] + dur,
                         start_times[i] >= as_,
                         end_times[i] <= ae_
                     ),
                     True)
        solver.add(cond)

    # For step i >= 1, arrival time is end_times[i-1] + travel time
    if i > 0:
        prev_fid = friends[i-1]
        curr_fid = friends[i]

        # Generate travel time expression based on previous and current friend IDs
        travel_time_expr = 0
        for p_id in range(11):  # 0-10
            p_loc = friends_locations.get(p_id, 'Union Square') if p_id != 0 else 'Union Square'
            for c_id in range(11):
                c_loc = friends_locations.get(c_id, 'Union Square') if c_id != 0 else 'Union Square'
                time = travel_time_dict.get(p_loc, {}).get(c_loc, 0)
                travel_time_expr = z3.If(z3.And(prev_fid == p_id, curr_fid == c_id), time, travel_time_expr)
        arrival_time = end_times[i-1] + travel_time_expr
        solver.add(start_times[i] >= arrival_time)

# Add constraints that no two friends are met more than once
for i in range(MAX_STEPS):
    for j in range(i+1, MAX_STEPS):
        solver.add(z3.Or(friends[i] == 0, friends[j] == 0, friends[i] != friends[j]))

opt = z3.Optimize()
for c in solver.assertions():
    opt.add(c)

objective = z3.Sum([z3.If(friends[i] != 0, 1, 0) for i in range(MAX_STEPS)])
opt.maximize(objective)

if opt.check() == z3.sat:
    model = opt.model()
    itinerary = []
    for i in range(MAX_STEPS):
        fid = model.eval(friends[i])
        if fid != 0:
            for f in friends_data:
                if f['id'] == fid:
                    st = model.eval(start_times[i])
                    et = model.eval(end_times[i])
                    start_h = st // 60
                    start_m = st % 60
                    end_h = et // 60
                    end_m = et % 60
                    itinerary.append({
                        'action': 'meet',
                        'person': f['name'],
                        'start_time': f"{start_h:02d}:{start_m:02d}",
                        'end_time': f"{end_h:02d}:{end_m:02d}"
                    })
                    break
    # Sort by start time
    itinerary.sort(key=lambda x: x['start_time'])
    print(json.dumps({'itinerary': itinerary}))
else:
    print("No solution found.")