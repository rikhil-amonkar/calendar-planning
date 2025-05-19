import json

def time_to_minutes(t_str):
    t_str = t_str.replace('AM', '').replace('PM', '').strip()
    if ':' in t_str:
        h, m = t_str.split(':')
    else:
        h, m = t_str, '00'
    h = int(h)
    m = int(m)
    if 'PM' in t_str.upper() and h != 12:
        h += 12
    if 'AM' in t_str.upper() and h == 12:
        h = 0
    return h * 60 + m

def minutes_to_time(mins):
    h = mins // 60
    m = mins % 60
    return f"{h}:{m:02d}".replace(':0', ':') if m == 0 else f"{h}:{m:02d}"

travel_times = {
    ('Union Square', 'Mission District'): 14,
    ('Union Square', 'Fisherman\'s Wharf'): 15,
    ('Union Square', 'Russian Hill'): 13,
    ('Union Square', 'Marina District'): 18,
    ('Union Square', 'North Beach'): 10,
    ('Union Square', 'Chinatown'): 7,
    ('Union Square', 'Pacific Heights'): 15,
    ('Union Square', 'The Castro'): 17,
    ('Union Square', 'Nob Hill'): 9,
    ('Union Square', 'Sunset District'): 27,
    ('Mission District', 'Union Square'): 15,
    ('Mission District', 'Fisherman\'s Wharf'): 22,
    ('Mission District', 'Russian Hill'): 15,
    ('Mission District', 'Marina District'): 19,
    ('Mission District', 'North Beach'): 17,
    ('Mission District', 'Chinatown'): 16,
    ('Mission District', 'Pacific Heights'): 16,
    ('Mission District', 'The Castro'): 7,
    ('Mission District', 'Nob Hill'): 12,
    ('Mission District', 'Sunset District'): 24,
    ('Fisherman\'s Wharf', 'Union Square'): 13,
    ('Fisherman\'s Wharf', 'Mission District'): 22,
    ('Fisherman\'s Wharf', 'Russian Hill'): 7,
    ('Fisherman\'s Wharf', 'Marina District'): 9,
    ('Fisherman\'s Wharf', 'North Beach'): 6,
    ('Fisherman\'s Wharf', 'Chinatown'): 12,
    ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
    ('Fisherman\'s Wharf', 'The Castro'): 27,
    ('Fisherman\'s Wharf', 'Nob Hill'): 11,
    ('Fisherman\'s Wharf', 'Sunset District'): 27,
    ('Russian Hill', 'Union Square'): 10,
    ('Russian Hill', 'Mission District'): 16,
    ('Russian Hill', 'Fisherman\'s Wharf'): 7,
    ('Russian Hill', 'Marina District'): 7,
    ('Russian Hill', 'North Beach'): 5,
    ('Russian Hill', 'Chinatown'): 9,
    ('Russian Hill', 'Pacific Heights'): 7,
    ('Russian Hill', 'The Castro'): 21,
    ('Russian Hill', 'Nob Hill'): 5,
    ('Russian Hill', 'Sunset District'): 23,
    ('Marina District', 'Union Square'): 16,
    ('Marina District', 'Mission District'): 20,
    ('Marina District', 'Fisherman\'s Wharf'): 10,
    ('Marina District', 'Russian Hill'): 8,
    ('Marina District', 'North Beach'): 11,
    ('Marina District', 'Chinatown'): 15,
    ('Marina District', 'Pacific Heights'): 7,
    ('Marina District', 'The Castro'): 22,
    ('Marina District', 'Nob Hill'): 12,
    ('Marina District', 'Sunset District'): 19,
    ('North Beach', 'Union Square'): 7,
    ('North Beach', 'Mission District'): 18,
    ('North Beach', 'Fisherman\'s Wharf'): 5,
    ('North Beach', 'Russian Hill'): 4,
    ('North Beach', 'Marina District'): 9,
    ('North Beach', 'Chinatown'): 6,
    ('North Beach', 'Pacific Heights'): 8,
    ('North Beach', 'The Castro'): 23,
    ('North Beach', 'Nob Hill'): 7,
    ('North Beach', 'Sunset District'): 27,
    ('Chinatown', 'Union Square'): 7,
    ('Chinatown', 'Mission District'): 17,
    ('Chinatown', 'Fisherman\'s Wharf'): 8,
    ('Chinatown', 'Russian Hill'): 7,
    ('Chinatown', 'Marina District'): 12,
    ('Chinatown', 'North Beach'): 3,
    ('Chinatown', 'Pacific Heights'): 10,
    ('Chinatown', 'The Castro'): 22,
    ('Chinatown', 'Nob Hill'): 9,
    ('Chinatown', 'Sunset District'): 29,
    ('Pacific Heights', 'Union Square'): 12,
    ('Pacific Heights', 'Mission District'): 15,
    ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
    ('Pacific Heights', 'Russian Hill'): 7,
    ('Pacific Heights', 'Marina District'): 6,
    ('Pacific Heights', 'North Beach'): 9,
    ('Pacific Heights', 'Chinatown'): 11,
    ('Pacific Heights', 'The Castro'): 16,
    ('Pacific Heights', 'Nob Hill'): 8,
    ('Pacific Heights', 'Sunset District'): 21,
    ('The Castro', 'Union Square'): 19,
    ('The Castro', 'Mission District'): 7,
    ('The Castro', 'Fisherman\'s Wharf'): 24,
    ('The Castro', 'Russian Hill'): 18,
    ('The Castro', 'Marina District'): 21,
    ('The Castro', 'North Beach'): 20,
    ('The Castro', 'Chinatown'): 22,
    ('The Castro', 'Pacific Heights'): 16,
    ('The Castro', 'Nob Hill'): 16,
    ('The Castro', 'Sunset District'): 17,
    ('Nob Hill', 'Union Square'): 7,
    ('Nob Hill', 'Mission District'): 13,
    ('Nob Hill', 'Fisherman\'s Wharf'): 10,
    ('Nob Hill', 'Russian Hill'): 5,
    ('Nob Hill', 'Marina District'): 11,
    ('Nob Hill', 'North Beach'): 8,
    ('Nob Hill', 'Chinatown'): 6,
    ('Nob Hill', 'Pacific Heights'): 8,
    ('Nob Hill', 'The Castro'): 17,
    ('Nob Hill', 'Sunset District'): 24,
    ('Sunset District', 'Union Square'): 30,
    ('Sunset District', 'Mission District'): 25,
    ('Sunset District', 'Fisherman\'s Wharf'): 29,
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'Marina District'): 21,
    ('Sunset District', 'North Beach'): 28,
    ('Sunset District', 'Chinatown'): 30,
    ('Sunset District', 'Pacific Heights'): 21,
    ('Sunset District', 'The Castro'): 17,
    ('Sunset District', 'Nob Hill'): 27,
}

friends = [
    {'name': 'Kevin', 'location': 'Mission District', 'start': time_to_minutes('8:45PM'), 'end': time_to_minutes('9:45PM'), 'duration': 60},
    {'name': 'Mark', 'location': 'Fisherman\'s Wharf', 'start': time_to_minutes('5:15PM'), 'end': time_to_minutes('8:00PM'), 'duration': 90},
    {'name': 'Jessica', 'location': 'Russian Hill', 'start': time_to_minutes('9:00AM'), 'end': time_to_minutes('3:00PM'), 'duration': 120},
    {'name': 'Jason', 'location': 'Marina District', 'start': time_to_minutes('3:15PM'), 'end': time_to_minutes('9:45PM'), 'duration': 120},
    {'name': 'John', 'location': 'North Beach', 'start': time_to_minutes('9:45AM'), 'end': time_to_minutes('6:00PM'), 'duration': 15},
    {'name': 'Karen', 'location': 'Chinatown', 'start': time_to_minutes('4:45PM'), 'end': time_to_minutes('7:00PM'), 'duration': 75},
    {'name': 'Sarah', 'location': 'Pacific Heights', 'start': time_to_minutes('5:30PM'), 'end': time_to_minutes('6:15PM'), 'duration': 45},
    {'name': 'Amanda', 'location': 'The Castro', 'start': time_to_minutes('8:00PM'), 'end': time_to_minutes('9:15PM'), 'duration': 60},
    {'name': 'Nancy', 'location': 'Nob Hill', 'start': time_to_minutes('9:45AM'), 'end': time_to_minutes('1:00PM'), 'duration': 45},
    {'name': 'Rebecca', 'location': 'Sunset District', 'start': time_to_minutes('8:45AM'), 'end': time_to_minutes('3:00PM'), 'duration': 75},
]

friends_sorted = sorted(friends, key=lambda x: x['end'])

itinerary = []
current_loc = 'Union Square'
current_time = time_to_minutes('9:00AM')

for friend in friends_sorted:
    from_loc = current_loc
    to_loc = friend['location']
    travel_time = travel_times.get((from_loc, to_loc))
    if travel_time is None:
        continue
    arrival = current_time + travel_time
    start = max(arrival, friend['start'])
    end = start + friend['duration']
    if end > friend['end']:
        continue
    itinerary.append({
        'action': 'meet',
        'location': to_loc,
        'person': friend['name'],
        'start_time': minutes_to_time(start).replace(':00', ''),
        'end_time': minutes_to_time(end).replace(':00', '')
    })
    current_time = end
    current_loc = to_loc

print(json.dumps({'itinerary': itinerary}, indent=2))