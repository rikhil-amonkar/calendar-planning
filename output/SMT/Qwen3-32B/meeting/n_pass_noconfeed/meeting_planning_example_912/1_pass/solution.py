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
    ('Presidio', 'Union Square'): 22,
    ('Presidio', 'Alamo Square'): 19,
    ('Presidio', 'Marina District'): 11,
    ('Presidio', 'Financial District'): 23,
    ('Presidio', 'Nob Hill'): 18,
    ('Presidio', 'Sunset District'): 15,
    ('Presidio', 'Chinatown'): 21,
    ('Presidio', 'Russian Hill'): 14,
    ('Presidio', 'North Beach'): 18,
    ('Presidio', 'Haight-Ashbury'): 15,
    ('Alamo Square', 'Union Square'): 14,
    ('Alamo Square', 'Presidio'): 17,
    ('Alamo Square', 'Marina District'): 15,
    ('Alamo Square', 'Financial District'): 17,
    ('Alamo Square', 'Nob Hill'): 11,
    ('Alamo Square', 'Sunset District'): 16,
    ('Alamo Square', 'Chinatown'): 15,
    ('Alamo Square', 'Russian Hill'): 13,
    ('Alamo Square', 'North Beach'): 15,
    ('Alamo Square', 'Haight-Ashbury'): 5,
    ('Marina District', 'Union Square'): 16,
    ('Marina District', 'Presidio'): 10,
    ('Marina District', 'Alamo Square'): 15,
    ('Marina District', 'Financial District'): 17,
    ('Marina District', 'Nob Hill'): 12,
    ('Marina District', 'Sunset District'): 19,
    ('Marina District', 'Chinatown'): 15,
    ('Marina District', 'Russian Hill'): 8,
    ('Marina District', 'North Beach'): 11,
    ('Marina District', 'Haight-Ashbury'): 16,
    ('Financial District', 'Union Square'): 9,
    ('Financial District', 'Presidio'): 22,
    ('Financial District', 'Alamo Square'): 17,
    ('Financial District', 'Marina District'): 15,
    ('Financial District', 'Nob Hill'): 8,
    ('Financial District', 'Sunset District'): 30,
    ('Financial District', 'Chinatown'): 5,
    ('Financial District', 'Russian Hill'): 11,
    ('Financial District', 'North Beach'): 7,
    ('Financial District', 'Haight-Ashbury'): 19,
    ('Nob Hill', 'Union Square'): 7,
    ('Nob Hill', 'Presidio'): 17,
    ('Nob Hill', 'Alamo Square'): 11,
    ('Nob Hill', 'Marina District'): 11,
    ('Nob Hill', 'Financial District'): 9,
    ('Nob Hill', 'Sunset District'): 24,
    ('Nob Hill', 'Chinatown'): 6,
    ('Nob Hill', 'Russian Hill'): 5,
    ('Nob Hill', 'North Beach'): 8,
    ('Nob Hill', 'Haight-Ashbury'): 13,
    ('Sunset District', 'Union Square'): 30,
    ('Sunset District', 'Presidio'): 16,
    ('Sunset District', 'Alamo Square'): 17,
    ('Sunset District', 'Marina District'): 21,
    ('Sunset District', 'Financial District'): 30,
    ('Sunset District', 'Nob Hill'): 27,
    ('Sunset District', 'Chinatown'): 30,
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'North Beach'): 28,
    ('Sunset District', 'Haight-Ashbury'): 15,
    ('Chinatown', 'Union Square'): 7,
    ('Chinatown', 'Presidio'): 19,
    ('Chinatown', 'Alamo Square'): 17,
    ('Chinatown', 'Marina District'): 12,
    ('Chinatown', 'Financial District'): 5,
    ('Chinatown', 'Nob Hill'): 9,
    ('Chinatown', 'Sunset District'): 30,
    ('Chinatown', 'Russian Hill'): 7,
    ('Chinatown', 'North Beach'): 3,
    ('Chinatown', 'Haight-Ashbury'): 19,
    ('Russian Hill', 'Union Square'): 10,
    ('Russian Hill', 'Presidio'): 14,
    ('Russian Hill', 'Alamo Square'): 15,
    ('Russian Hill', 'Marina District'): 7,
    ('Russian Hill', 'Financial District'): 11,
    ('Russian Hill', 'Nob Hill'): 5,
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'Chinatown'): 9,
    ('Russian Hill', 'North Beach'): 5,
    ('Russian Hill', 'Haight-Ashbury'): 17,
    ('North Beach', 'Union Square'): 7,
    ('North Beach', 'Presidio'): 17,
    ('North Beach', 'Alamo Square'): 16,
    ('North Beach', 'Marina District'): 9,
    ('North Beach', 'Financial District'): 8,
    ('North Beach', 'Nob Hill'): 7,
    ('North Beach', 'Sunset District'): 27,
    ('North Beach', 'Chinatown'): 6,
    ('North Beach', 'Russian Hill'): 4,
    ('North Beach', 'Haight-Ashbury'): 18,
    ('Haight-Ashbury', 'Union Square'): 19,
    ('Haight-Ashbury', 'Presidio'): 15,
    ('Haight-Ashbury', 'Alamo Square'): 5,
    ('Haight-Ashbury', 'Marina District'): 17,
    ('Haight-Ashbury', 'Financial District'): 21,
    ('Haight-Ashbury', 'Nob Hill'): 15,
    ('Haight-Ashbury', 'Sunset District'): 15,
    ('Haight-Ashbury', 'Chinatown'): 19,
    ('Haight-Ashbury', 'Russian Hill'): 17,
    ('Haight-Ashbury', 'North Beach'): 19,
}

solver = z3.Solver()

initial_time = 540  # 9:00 AM in minutes

start_times = {}
end_times = {}
for name, data in friends.items():
    start = z3.Int(f'start_{name}')
    duration = data['min_duration']
    end = start + duration
    start_times[name] = start
    end_times[name] = end
    available_start = data['available_start']
    available_end = data['available_end']
    solver.add(start >= available_start)
    solver.add(end <= available_end)

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
        
        dataA = friends[nameA]
        available_start_A = dataA['available_start']
        available_end_A = dataA['available_end']
        
        dataB = friends[nameB]
        available_start_B = dataB['available_start']
        available_end_B = dataB['available_end']
        
        solver.add(z3.Implies(
            z3.And(
                z3.And(startA >= available_start_A, endA <= available_end_A),
                z3.And(startB >= available_start_B, endB <= available_end_B)
            ),
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
    endA = end_times[nameA]
    available_start_A = dataA['available_start']
    available_end_A = dataA['available_end']
    
    disjunction = [startA >= initial_time + travel_union_to_A]
    
    for nameB in friends:
        if nameB == nameA:
            continue
        locB = friends[nameB]['location']
        travel_B_to_A = travel_times.get((locB, locA), 0)
        endB = end_times[nameB]
        disjunction.append(endB + travel_B_to_A <= startA)
    
    solver.add(z3.Implies(
        z3.And(startA >= available_start_A, endA <= available_end_A),
        z3.Or(*disjunction)
    ))

# Check if the constraints are satisfiable
if solver.check() == z3.sat:
    model = solver.model()
    # Extract the visited friends
    visited = []
    for name in friends:
        start = model[start_times[name]]
        available_start = friends[name]['available_start']
        available_end = friends[name]['available_end']
        duration = friends[name]['min_duration']
        end = start + duration
        # Check if start and end are within the availability
        if start.as_long() >= available_start and end.as_long() <= available_end:
            visited.append({
                'name': name,
                'start': start.as_long(),
                'end': end.as_long()
            })
    # Sort visited by start time
    visited.sort(key=lambda x: x['start'])
    # Convert to the required JSON format
    itinerary = []
    for item in visited:
        name = item['name']
        start_time = item['start']
        end_time = item['end']
        # Convert to H:MM format
        def to_time_str(minutes):
            hours = minutes // 60
            mins = minutes % 60
            return f"{hours}:{mins:02d}"
        itinerary.append({
            "action": "meet",
            "location": friends[name]['location'],
            "person": name,
            "start_time": to_time_str(start_time),
            "end_time": to_time_str(end_time)
        })
    # Output JSON
    print(json.dumps({"itinerary": itinerary}))
else:
    print("No solution found.")