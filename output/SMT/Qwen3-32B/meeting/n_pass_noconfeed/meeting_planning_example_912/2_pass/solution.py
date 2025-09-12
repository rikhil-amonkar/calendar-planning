import z3
import json

friends = {
    'Kimberly': {
        'location': 'Presidio',
        'available_start': 930,
        'available_end': 960,
        'min_duration': 15
    },
    'Elizabeth': {
        'location': 'Alamo Square',
        'available_start': 1155,
        'available_end': 1215,
        'min_duration': 15
    },
    'Joshua': {
        'location': 'Marina District',
        'available_start': 630,
        'available_end': 855,
        'min_duration': 45
    },
    'Sandra': {
        'location': 'Financial District',
        'available_start': 1170,
        'available_end': 1215,
        'min_duration': 45
    },
    'Kenneth': {
        'location': 'Nob Hill',
        'available_start': 765,
        'available_end': 1275,
        'min_duration': 30
    },
    'Betty': {
        'location': 'Sunset District',
        'available_start': 840,
        'available_end': 1140,
        'min_duration': 60
    },
    'Deborah': {
        'location': 'Chinatown',
        'available_start': 915,
        'available_end': 1230,
        'min_duration': 15
    },
    'Barbara': {
        'location': 'Russian Hill',
        'available_start': 1050,
        'available_end': 1275,
        'min_duration': 120
    },
    'Steven': {
        'location': 'North Beach',
        'available_start': 1065,
        'available_end': 1245,
        'min_duration': 90
    },
    'Daniel': {
        'location': 'Haight-Ashbury',
        'available_start': 1110,
        'available_end': 1125,
        'min_duration': 15
    }
}

travel_times = {
    ('Union Square', 'Presidio'): 24,
    ('Union Square', 'Alamo Square'): 15,
    ('Union Square', 'Marina District'): 18,
    ('Union Square', 'Financial District'): 9,
    ('Union Square', 'Nob Hill'): 9,
    ('Union Square', 'Sunset District'): 27,
    ('Union Square', 'Chinatown'): 7,
    ('Union Square', 'Russian Hill'): 13,
    ('Union Square', 'North Beach'): 10,
    ('Union Square', 'Haight-Ashbury'): 18,
    # Reverse directions also included in the original data
    # ... (omitted for brevity)
}

solver = z3.Solver()

initial_time = 540  # 9:00 AM in minutes

start_times = {}
end_times = {}
visited = {}

for name, data in friends.items():
    start = z3.Int(f'start_{name}')
    duration = data['min_duration']
    end = start + duration
    start_times[name] = start
    end_times[name] = end
    visited[name] = z3.Bool(f'visited_{name}')
    available_start = data['available_start']
    available_end = data['available_end']
    solver.add(z3.Implies(visited[name], start >= available_start))
    solver.add(z3.Implies(visited[name], end <= available_end))

# Add pairwise constraints for order and travel times
for nameA in friends:
    for nameB in friends:
        if nameA == nameB:
            continue
        locA = friends[nameA]['location']
        locB = friends[nameB]['location']
        travel_AB = travel_times.get((locA, locB), 0)
        endA = end_times[nameA]
        startB = start_times[nameB]
        endB = end_times[nameB]
        startA = start_times[nameA]
        travel_BA = travel_times.get((locB, locA), 0)
        solver.add(z3.Implies(
            z3.And(visited[nameA], visited[nameB]),
            z3.Or(
                endA + travel_AB <= startB,
                endB + travel_BA <= startA
            )
        ))

# Add constraints for initial travel time for each friend
for nameA in friends:
    dataA = friends[nameA]
    locA = dataA['location']
    travel_union_to_A = travel_times[('Union Square', locA)]
    startA = start_times[nameA]
    disjunction = [startA >= initial_time + travel_union_to_A]
    for nameB in friends:
        if nameB == nameA:
            continue
        locB = friends[nameB]['location']
        travel_B_to_A = travel_times.get((locB, locA), 0)
        endB = end_times[nameB]
        disjunction.append(endB + travel_B_to_A <= startA)
    solver.add(z3.Implies(visited[nameA], z3.Or(*disjunction)))

# Ensure at least one friend is visited
solver.add(z3.Or([visited[name] for name in friends]))

# Check if the constraints are satisfiable
if solver.check() == z3.sat:
    model = solver.model()
    visited_names = [name for name in friends if model.eval(visited[name])]
    visited_meetings = []
    for name in visited_names:
        start = model[start_times[name]]
        duration = friends[name]['min_duration']
        end = start + duration
        visited_meetings.append({
            'name': name,
            'start': start.as_long(),
            'end': end.as_long()
        })
    visited_meetings.sort(key=lambda x: x['start'])

    def to_time_str(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours}:{mins:02d}"

    itinerary = []
    for item in visited_meetings:
        itinerary.append({
            "action": "meet",
            "location": friends[item['name']]['location'],
            "person": item['name'],
            "start_time": to_time_str(item['start']),
            "end_time": to_time_str(item['end'])
        })
    print(json.dumps({"itinerary": itinerary}))
else:
    print("No solution found.")