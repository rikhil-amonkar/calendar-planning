import z3
import json

def minutes_to_time(minutes):
    base_hour = 9
    total_minutes = minutes
    hours = base_hour + (total_minutes // 60)
    minutes = total_minutes % 60
    return f"{int(hours):02d}:{int(minutes):02d}"

travel_time_dict = {
    ('Pacific Heights', 'Nob Hill'): 8,
    ('Pacific Heights', 'Russian Hill'): 7,
    ('Pacific Heights', 'The Castro'): 16,
    ('Pacific Heights', 'Sunset District'): 21,
    ('Pacific Heights', 'Haight-Ashbury'): 11,
    ('Nob Hill', 'Pacific Heights'): 8,
    ('Nob Hill', 'Russian Hill'): 5,
    ('Nob Hill', 'The Castro'): 17,
    ('Nob Hill', 'Sunset District'): 25,
    ('Nob Hill', 'Haight-Ashbury'): 13,
    ('Russian Hill', 'Pacific Heights'): 7,
    ('Russian Hill', 'Nob Hill'): 5,
    ('Russian Hill', 'The Castro'): 21,
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'Haight-Ashbury'): 17,
    ('The Castro', 'Pacific Heights'): 16,
    ('The Castro', 'Nob Hill'): 16,
    ('The Castro', 'Russian Hill'): 18,
    ('The Castro', 'Sunset District'): 17,
    ('The Castro', 'Haight-Ashbury'): 6,
    ('Sunset District', 'Pacific Heights'): 21,
    ('Sunset District', 'Nob Hill'): 27,
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'The Castro'): 17,
    ('Sunset District', 'Haight-Ashbury'): 15,
    ('Haight-Ashbury', 'Pacific Heights'): 12,
    ('Haight-Ashbury', 'Nob Hill'): 15,
    ('Haight-Ashbury', 'Russian Hill'): 17,
    ('Haight-Ashbury', 'The Castro'): 6,
    ('Haight-Ashbury', 'Sunset District'): 15
}

friends = ['Ronald', 'Helen', 'Joshua', 'Margaret']
locations = {
    'Ronald': 'Nob Hill',
    'Helen': 'The Castro',
    'Joshua': 'Sunset District',
    'Margaret': 'Haight-Ashbury'
}
durations = {
    'Ronald': 105,
    'Helen': 120,
    'Joshua': 90,
    'Margaret': 60
}
availability_start = {
    'Ronald': 60,    # 10:00 AM
    'Helen': 270,    # 1:30 PM
    'Joshua': 315,   # 2:15 PM
    'Margaret': 75   # 10:15 AM
}
availability_end = {
    'Ronald': 480,   # 5:00 PM
    'Helen': 480,    # 5:00 PM
    'Joshua': 630,   # 7:30 PM
    'Margaret': 780  # 10:00 PM
}

solver = z3.Solver()

start_times = {friend: z3.Int(f'start_{friend}') for friend in friends}
positions = {friend: z3.Int(f'pos_{friend}') for friend in friends}

for friend in friends:
    solver.add(positions[friend] >= 0, positions[friend] < len(friends))
solver.add(z3.Distinct([positions[friend] for friend in friends]))

for friend in friends:
    solver.add(start_times[friend] >= availability_start[friend])
    solver.add(start_times[friend] + durations[friend] <= availability_end[friend])

for friend in friends:
    travel_from_start = travel_time_dict[('Pacific Heights', locations[friend])]
    solver.add(z3.Implies(positions[friend] == 0, start_times[friend] >= travel_from_start))

for friend1 in friends:
    for friend2 in friends:
        if friend1 == friend2:
            continue
        travel_time = travel_time_dict[(locations[friend1], locations[friend2])]
        is_consecutive = z3.And(positions[friend2] == positions[friend1] + 1)
        end_plus_travel = start_times[friend1] + durations[friend1] + travel_time
        solver.add(z3.Implies(is_consecutive, start_times[friend2] >= end_plus_travel))

# Add return time constraint (must return to Pacific Heights by 10:00 PM)
for friend in friends:
    is_last = (positions[friend] == len(friends) - 1)  # Fixed missing parenthesis
    travel_back = travel_time_dict[(locations[friend], 'Pacific Heights')]
    return_time = start_times[friend] + durations[friend] + travel_back
    solver.add(z3.Implies(is_last, return_time <= 780))  # 10:00 PM = 780 minutes

if solver.check() == z3.sat:
    model = solver.model()
    schedule = []
    for friend in friends:
        start_val = model.eval(start_times[friend]).as_long()
        end_val = start_val + durations[friend]
        schedule.append({
            'person': friend,
            'start_time': minutes_to_time(start_val),
            'end_time': minutes_to_time(end_val),
            'pos': model.eval(positions[friend]).as_long()
        })
    
    schedule.sort(key=lambda x: x['pos'])
    itinerary = [{
        "action": "meet",
        "person": item['person'],
        "start_time": item['start_time'],
        "end_time": item['end_time']
    } for item in schedule]
    
    result = {"itinerary": itinerary}
    print("SOLUTION:")
    print(json.dumps(result))
else:
    print("SOLUTION:")
    print(json.dumps({"itinerary": []}))