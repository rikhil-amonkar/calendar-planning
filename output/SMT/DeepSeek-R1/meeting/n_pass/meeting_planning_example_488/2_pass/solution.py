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
    'Ronald': 60,    # 10:00 AM (60 minutes after 9:00 AM)
    'Helen': 270,    # 1:30 PM (270 minutes after 9:00 AM)
    'Joshua': 315,   # 2:15 PM (315 minutes after 9:00 AM)
    'Margaret': 75   # 10:15 AM (75 minutes after 9:00 AM)
}

availability_end = {
    'Ronald': 480,   # 5:00 PM (480 minutes after 9:00 AM)
    'Helen': 480,    # 5:00 PM (480 minutes after 9:00 AM)
    'Joshua': 630,   # 7:30 PM (630 minutes after 9:00 AM)
    'Margaret': 780  # 10:00 PM (780 minutes after 9:00 AM)
}

solver = z3.Solver()

start_times = {friend: z3.Int(f'start_{friend}') for friend in friends}
positions = {friend: z3.Int(f'pos_{friend}') for friend in friends}

for friend in friends:
    solver.add(positions[friend] >= 0)
    solver.add(positions[friend] <= 3)

solver.add(z3.Distinct([positions[friend] for friend in friends]))

for friend in friends:
    solver.add(start_times[friend] >= availability_start[friend])
    solver.add(start_times[friend] + durations[friend] <= availability_end[friend])

for friend in friends:
    travel_from_start = travel_time_dict[('Pacific Heights', locations[friend])]
    solver.add(z3.Implies(positions[friend] == 0, start_times[friend] >= travel_from_start))

for friend1 in friends:
    for friend2 in friends:
        if friend1 != friend2:
            travel_time = travel_time_dict[(locations[friend1], locations[friend2])]
            condition = z3.And(positions[friend2] == positions[friend1] + 1)
            constraint = start_times[friend2] >= start_times[friend1] + durations[friend1] + travel_time
            solver.add(z3.Implies(condition, constraint))

if solver.check() == z3.sat:
    model = solver.model()
    schedule = []
    for friend in friends:
        start_val = model.eval(start_times[friend]).as_long()
        end_val = start_val + durations[friend]
        schedule.append({
            'person': friend,
            'start_time': minutes_to_time(start_val),
            'end_time': minutes_to_time(end_val)
        })
    
    schedule.sort(key=lambda x: x['start_time'])
    
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