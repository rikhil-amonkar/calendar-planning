import json

def time_to_minutes(t):
    hours, mins = map(int, t.split(':'))
    return hours * 60 + mins

def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

friends = [
    {'name': 'Elizabeth', 'location': 'Mission District', 'start': time_to_minutes('10:30'), 'end': time_to_minutes('20:00'), 'duration': 90},
    {'name': 'David', 'location': 'Union Square', 'start': time_to_minutes('15:15'), 'end': time_to_minutes('19:00'), 'duration': 45},
    {'name': 'Sandra', 'location': 'Pacific Heights', 'start': time_to_minutes('7:00'), 'end': time_to_minutes('20:00'), 'duration': 120},
    {'name': 'Thomas', 'location': 'Bayview', 'start': time_to_minutes('19:30'), 'end': time_to_minutes('20:30'), 'duration': 30},
    {'name': 'Robert', 'location': 'Fisherman\'s Wharf', 'start': time_to_minutes('10:00'), 'end': time_to_minutes('15:00'), 'duration': 15},
    {'name': 'Kenneth', 'location': 'Marina District', 'start': time_to_minutes('10:45'), 'end': time_to_minutes('13:00'), 'duration': 45},
    {'name': 'Melissa', 'location': 'Richmond District', 'start': time_to_minutes('18:15'), 'end': time_to_minutes('20:00'), 'duration': 15},
    {'name': 'Kimberly', 'location': 'Sunset District', 'start': time_to_minutes('10:15'), 'end': time_to_minutes('18:15'), 'duration': 105},
    {'name': 'Amanda', 'location': 'Golden Gate Park', 'start': time_to_minutes('7:45'), 'end': time_to_minutes('18:45'), 'duration': 15}
]

travel_times = {
    ('Haight-Ashbury', 'Mission District'): 11,
    ('Haight-Ashbury', 'Union Square'): 19,
    ('Haight-Ashbury', 'Pacific Heights'): 12,
    ('Haight-Ashbury', 'Bayview'): 18,
    ('Haight-Ashbury', 'Fisherman\'s Wharf'): 23,
    ('Haight-Ashbury', 'Marina District'): 17,
    ('Haight-Ashbury', 'Richmond District'): 10,
    ('Haight-Ashbury', 'Sunset District'): 15,
    ('Haight-Ashbury', 'Golden Gate Park'): 7,
    ('Mission District', 'Haight-Ashbury'): 12,
    ('Mission District', 'Union Square'): 15,
    ('Mission District', 'Pacific Heights'): 16,
    ('Mission District', 'Bayview'): 14,
    ('Mission District', 'Fisherman\'s Wharf'): 22,
    ('Mission District', 'Marina District'): 19,
    ('Mission District', 'Richmond District'): 20,
    ('Mission District', 'Sunset District'): 24,
    ('Mission District', 'Golden Gate Park'): 17,
    ('Union Square', 'Haight-Ashbury'): 18,
    ('Union Square', 'Mission District'): 14,
    ('Union Square', 'Pacific Heights'): 15,
    ('Union Square', 'Bayview'): 15,
    ('Union Square', 'Fisherman\'s Wharf'): 15,
    ('Union Square', 'Marina District'): 18,
    ('Union Square', 'Richmond District'): 20,
    ('Union Square', 'Sunset District'): 27,
    ('Union Square', 'Golden Gate Park'): 22,
    ('Pacific Heights', 'Haight-Ashbury'): 11,
    ('Pacific Heights', 'Mission District'): 15,
    ('Pacific Heights', 'Union Square'): 12,
    ('Pacific Heights', 'Bayview'): 22,
    ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
    ('Pacific Heights', 'Marina District'): 6,
    ('Pacific Heights', 'Richmond District'): 12,
    ('Pacific Heights', 'Sunset District'): 21,
    ('Pacific Heights', 'Golden Gate Park'): 15,
    ('Bayview', 'Haight-Ashbury'): 19,
    ('Bayview', 'Mission District'): 13,
    ('Bayview', 'Union Square'): 18,
    ('Bayview', 'Pacific Heights'): 23,
    ('Bayview', 'Fisherman\'s Wharf'): 25,
    ('Bayview', 'Marina District'): 27,
    ('Bayview', 'Richmond District'): 25,
    ('Bayview', 'Sunset District'): 23,
    ('Bayview', 'Golden Gate Park'): 22,
    ('Fisherman\'s Wharf', 'Haight-Ashbury'): 22,
    ('Fisherman\'s Wharf', 'Mission District'): 22,
    ('Fisherman\'s Wharf', 'Union Square'): 13,
    ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
    ('Fisherman\'s Wharf', 'Bayview'): 26,
    ('Fisherman\'s Wharf', 'Marina District'): 9,
    ('Fisherman\'s Wharf', 'Richmond District'): 18,
    ('Fisherman\'s Wharf', 'Sunset District'): 27,
    ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
    ('Marina District', 'Haight-Ashbury'): 16,
    ('Marina District', 'Mission District'): 20,
    ('Marina District', 'Union Square'): 16,
    ('Marina District', 'Pacific Heights'): 7,
    ('Marina District', 'Bayview'): 27,
    ('Marina District', 'Fisherman\'s Wharf'): 10,
    ('Marina District', 'Richmond District'): 11,
    ('Marina District', 'Sunset District'): 19,
    ('Marina District', 'Golden Gate Park'): 18,
    ('Richmond District', 'Haight-Ashbury'): 10,
    ('Richmond District', 'Mission District'): 20,
    ('Richmond District', 'Union Square'): 21,
    ('Richmond District', 'Pacific Heights'): 10,
    ('Richmond District', 'Bayview'): 27,
    ('Richmond District', 'Fisherman\'s Wharf'): 18,
    ('Richmond District', 'Marina District'): 9,
    ('Richmond District', 'Sunset District'): 11,
    ('Richmond District', 'Golden Gate Park'): 9,
    ('Sunset District', 'Haight-Ashbury'): 15,
    ('Sunset District', 'Mission District'): 25,
    ('Sunset District', 'Union Square'): 30,
    ('Sunset District', 'Pacific Heights'): 21,
    ('Sunset District', 'Bayview'): 22,
    ('Sunset District', 'Fisherman\'s Wharf'): 29,
    ('Sunset District', 'Marina District'): 21,
    ('Sunset District', 'Richmond District'): 12,
    ('Sunset District', 'Golden Gate Park'): 11,
    ('Golden Gate Park', 'Haight-Ashbury'): 7,
    ('Golden Gate Park', 'Mission District'): 17,
    ('Golden Gate Park', 'Union Square'): 22,
    ('Golden Gate Park', 'Pacific Heights'): 16,
    ('Golden Gate Park', 'Bayview'): 23,
    ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
    ('Golden Gate Park', 'Marina District'): 16,
    ('Golden Gate Park', 'Richmond District'): 7,
    ('Golden Gate Park', 'Sunset District'): 10
}

best_itinerary = []
max_met = 0

def backtrack(current_loc, current_time, met, path):
    global best_itinerary, max_met
    if len(met) > max_met:
        max_met = len(met)
        best_itinerary = path.copy()
        if max_met == len(friends):
            return True
    for friend in friends:
        name = friend['name']
        if name in met:
            continue
        travel = travel_times.get((current_loc, friend['location']), float('inf'))
        if travel == float('inf'):
            continue
        arrival = current_time + travel
        start = max(arrival, friend['start'])
        end = start + friend['duration']
        if end > friend['end']:
            continue
        new_met = met.copy()
        new_met.add(name)
        new_path = path.copy()
        new_path.append({
            'action': 'meet',
            'location': friend['location'],
            'person': name,
            'start_time': minutes_to_time(start),
            'end_time': minutes_to_time(end)
        })
        if backtrack(friend['location'], end, new_met, new_path):
            return True
    return False

backtrack('Haight-Ashbury', time_to_minutes('9:00'), set(), [])

print(json.dumps({'itinerary': best_itinerary}, indent=2))