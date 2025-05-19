import json

def time_to_min(t):
    hours, mins = map(int, t.split(':'))
    return hours * 60 + mins

def min_to_time(m):
    return f"{m // 60}:{m % 60:02d}"

friends = [
    {'name': 'Laura', 'location': 'Alamo Square', 'start': time_to_min('14:30'), 'end': time_to_min('16:15'), 'duration': 75},
    {'name': 'Brian', 'location': 'Presidio', 'start': time_to_min('10:15'), 'end': time_to_min('17:00'), 'duration': 30},
    {'name': 'Karen', 'location': 'Russian Hill', 'start': time_to_min('18:00'), 'end': time_to_min('20:15'), 'duration': 90},
    {'name': 'Stephanie', 'location': 'North Beach', 'start': time_to_min('10:15'), 'end': time_to_min('16:00'), 'duration': 75},
    {'name': 'Helen', 'location': 'Golden Gate Park', 'start': time_to_min('11:30'), 'end': time_to_min('21:45'), 'duration': 120},
    {'name': 'Sandra', 'location': 'Richmond District', 'start': time_to_min('8:00'), 'end': time_to_min('15:15'), 'duration': 30},
    {'name': 'Mary', 'location': 'Embarcadero', 'start': time_to_min('16:45'), 'end': time_to_min('18:45'), 'duration': 120},
    {'name': 'Deborah', 'location': 'Financial District', 'start': time_to_min('19:00'), 'end': time_to_min('20:45'), 'duration': 105},
    {'name': 'Elizabeth', 'location': 'Marina District', 'start': time_to_min('8:30'), 'end': time_to_min('13:15'), 'duration': 105},
]

for f in friends:
    f['latest_start'] = f['end'] - f['duration']

travel_times = {
    'Mission District': {'Alamo Square': 11, 'Presidio': 25, 'Russian Hill': 15, 'North Beach': 17, 'Golden Gate Park': 17, 'Richmond District': 20, 'Embarcadero': 19, 'Financial District': 15, 'Marina District': 19},
    'Alamo Square': {'Mission District': 10, 'Presidio': 17, 'Russian Hill': 13, 'North Beach': 15, 'Golden Gate Park': 9, 'Richmond District': 11, 'Embarcadero': 16, 'Financial District': 17, 'Marina District': 15},
    'Presidio': {'Mission District': 26, 'Alamo Square': 19, 'Russian Hill': 14, 'North Beach': 18, 'Golden Gate Park': 12, 'Richmond District': 7, 'Embarcadero': 20, 'Financial District': 23, 'Marina District': 11},
    'Russian Hill': {'Mission District': 16, 'Alamo Square': 15, 'Presidio': 14, 'North Beach': 5, 'Golden Gate Park': 21, 'Richmond District': 14, 'Embarcadero': 8, 'Financial District': 11, 'Marina District': 7},
    'North Beach': {'Mission District': 18, 'Alamo Square': 16, 'Presidio': 17, 'Russian Hill': 4, 'Golden Gate Park': 22, 'Richmond District': 18, 'Embarcadero': 6, 'Financial District': 8, 'Marina District': 9},
    'Golden Gate Park': {'Mission District': 17, 'Alamo Square': 9, 'Presidio': 11, 'Russian Hill': 19, 'North Beach': 23, 'Richmond District': 7, 'Embarcadero': 25, 'Financial District': 26, 'Marina District': 16},
    'Richmond District': {'Mission District': 20, 'Alamo Square': 13, 'Presidio': 7, 'Russian Hill': 13, 'North Beach': 17, 'Golden Gate Park': 9, 'Embarcadero': 19, 'Financial District': 22, 'Marina District': 9},
    'Embarcadero': {'Mission District': 20, 'Alamo Square': 19, 'Presidio': 20, 'Russian Hill': 8, 'North Beach': 5, 'Golden Gate Park': 25, 'Richmond District': 21, 'Financial District': 5, 'Marina District': 12},
    'Financial District': {'Mission District': 17, 'Alamo Square': 17, 'Presidio': 22, 'Russian Hill': 11, 'North Beach': 7, 'Golden Gate Park': 23, 'Richmond District': 21, 'Embarcadero': 4, 'Marina District': 15},
    'Marina District': {'Mission District': 20, 'Alamo Square': 15, 'Presidio': 10, 'Russian Hill': 8, 'North Beach': 11, 'Golden Gate Park': 18, 'Richmond District': 11, 'Embarcadero': 14, 'Financial District': 17},
}

best_schedule = []
best_count = 0
best_duration = 0

def backtrack(current_time, current_loc, visited, schedule):
    global best_schedule, best_count, best_duration
    if len(visited) > best_count or (len(visited) == best_count and sum(f['duration'] for f in schedule) > best_duration):
        best_schedule = schedule.copy()
        best_count = len(visited)
        best_duration = sum(f['duration'] for f in schedule)
    for i, friend in enumerate(friends):
        if i not in visited:
            tt = travel_times[current_loc].get(friend['location'], float('inf'))
            arrival = current_time + tt
            start = max(arrival, friend['start'])
            if start > friend['latest_start']:
                continue
            end = start + friend['duration']
            if end > friend['end']:
                continue
            new_schedule = schedule + [{
                'action': 'meet',
                'location': friend['location'],
                'person': friend['name'],
                'start_time': min_to_time(start).replace(':0', ':') if min_to_time(start).endswith(':00') else min_to_time(start).lstrip('0'),
                'end_time': min_to_time(end).replace(':0', ':') if min_to_time(end).endswith(':00') else min_to_time(end).lstrip('0')
            }]
            new_time = end
            new_loc = friend['location']
            new_visited = visited | {i}
            backtrack(new_time, new_loc, new_visited, new_schedule)

backtrack(540, 'Mission District', set(), [])

output = {
    "itinerary": best_schedule
}

print(json.dumps(output, indent=2))