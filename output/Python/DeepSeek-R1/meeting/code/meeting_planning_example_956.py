import json

def time_to_minutes(timestr):
    hours, minutes = map(int, timestr.replace('AM', '').replace('PM', '').split(':'))
    if 'PM' in timestr and hours != 12:
        hours += 12
    if 'AM' in timestr and hours == 12:
        hours = 0
    return hours * 60 + minutes

def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

travel_times = {
    'The Castro': {'Alamo Square': 8, 'Richmond District': 16, 'Financial District': 21, 'Union Square': 19, 'Fisherman\'s Wharf': 24, 'Marina District': 21, 'Haight-Ashbury': 6, 'Mission District': 7, 'Pacific Heights': 16, 'Golden Gate Park': 11},
    'Alamo Square': {'The Castro': 8, 'Richmond District': 11, 'Financial District': 17, 'Union Square': 14, 'Fisherman\'s Wharf': 19, 'Marina District': 15, 'Haight-Ashbury': 5, 'Mission District': 10, 'Pacific Heights': 10, 'Golden Gate Park': 9},
    'Richmond District': {'The Castro': 16, 'Alamo Square': 13, 'Financial District': 22, 'Union Square': 21, 'Fisherman\'s Wharf': 18, 'Marina District': 9, 'Haight-Ashbury': 10, 'Mission District': 20, 'Pacific Heights': 10, 'Golden Gate Park': 9},
    'Financial District': {'The Castro': 20, 'Alamo Square': 17, 'Richmond District': 21, 'Union Square': 9, 'Fisherman\'s Wharf': 10, 'Marina District': 15, 'Haight-Ashbury': 19, 'Mission District': 17, 'Pacific Heights': 13, 'Golden Gate Park': 23},
    'Union Square': {'The Castro': 17, 'Alamo Square': 15, 'Richmond District': 20, 'Financial District': 9, 'Fisherman\'s Wharf': 15, 'Marina District': 18, 'Haight-Ashbury': 18, 'Mission District': 14, 'Pacific Heights': 15, 'Golden Gate Park': 22},
    'Fisherman\'s Wharf': {'The Castro': 27, 'Alamo Square': 21, 'Richmond District': 18, 'Financial District': 11, 'Union Square': 13, 'Marina District': 9, 'Haight-Ashbury': 22, 'Mission District': 22, 'Pacific Heights': 12, 'Golden Gate Park': 25},
    'Marina District': {'The Castro': 22, 'Alamo Square': 15, 'Richmond District': 11, 'Financial District': 17, 'Union Square': 16, 'Fisherman\'s Wharf': 10, 'Haight-Ashbury': 16, 'Mission District': 20, 'Pacific Heights': 7, 'Golden Gate Park': 18},
    'Haight-Ashbury': {'The Castro': 6, 'Alamo Square': 5, 'Richmond District': 10, 'Financial District': 21, 'Union Square': 19, 'Fisherman\'s Wharf': 23, 'Marina District': 17, 'Mission District': 11, 'Pacific Heights': 12, 'Golden Gate Park': 7},
    'Mission District': {'The Castro': 7, 'Alamo Square': 11, 'Richmond District': 20, 'Financial District': 15, 'Union Square': 15, 'Fisherman\'s Wharf': 22, 'Marina District': 19, 'Haight-Ashbury': 12, 'Pacific Heights': 16, 'Golden Gate Park': 17},
    'Pacific Heights': {'The Castro': 16, 'Alamo Square': 10, 'Richmond District': 12, 'Financial District': 13, 'Union Square': 12, 'Fisherman\'s Wharf': 13, 'Marina District': 6, 'Haight-Ashbury': 11, 'Mission District': 15, 'Golden Gate Park': 15},
    'Golden Gate Park': {'The Castro': 13, 'Alamo Square': 9, 'Richmond District': 7, 'Financial District': 26, 'Union Square': 22, 'Fisherman\'s Wharf': 24, 'Marina District': 16, 'Haight-Ashbury': 7, 'Mission District': 17, 'Pacific Heights': 16}
}

friends = [
    {'name': 'William', 'location': 'Alamo Square', 'start': time_to_minutes('3:15PM'), 'end': time_to_minutes('5:15PM'), 'duration': 60},
    {'name': 'Joshua', 'location': 'Richmond District', 'start': time_to_minutes('7:00AM'), 'end': time_to_minutes('8:00PM'), 'duration': 15},
    {'name': 'Joseph', 'location': 'Financial District', 'start': time_to_minutes('11:15AM'), 'end': time_to_minutes('1:30PM'), 'duration': 15},
    {'name': 'David', 'location': 'Union Square', 'start': time_to_minutes('4:45PM'), 'end': time_to_minutes('7:15PM'), 'duration': 45},
    {'name': 'Brian', 'location': 'Fisherman\'s Wharf', 'start': time_to_minutes('1:45PM'), 'end': time_to_minutes('8:45PM'), 'duration': 105},
    {'name': 'Karen', 'location': 'Marina District', 'start': time_to_minutes('11:30AM'), 'end': time_to_minutes('6:30PM'), 'duration': 15},
    {'name': 'Anthony', 'location': 'Haight-Ashbury', 'start': time_to_minutes('7:15AM'), 'end': time_to_minutes('10:30AM'), 'duration': 30},
    {'name': 'Matthew', 'location': 'Mission District', 'start': time_to_minutes('5:15PM'), 'end': time_to_minutes('7:15PM'), 'duration': 120},
    {'name': 'Helen', 'location': 'Pacific Heights', 'start': time_to_minutes('8:00AM'), 'end': time_to_minutes('12:00PM'), 'duration': 75},
    {'name': 'Jeffrey', 'location': 'Golden Gate Park', 'start': time_to_minutes('7:00PM'), 'end': time_to_minutes('9:30PM'), 'duration': 60}
]

current_time = time_to_minutes('9:00AM')
current_location = 'The Castro'
itinerary = []
remaining = friends.copy()

while True:
    candidates = []
    for friend in remaining:
        loc = friend['location']
        if current_location not in travel_times or loc not in travel_times[current_location]:
            continue
        travel_time = travel_times[current_location][loc]
        arrival = current_time + travel_time
        start = max(arrival, friend['start'])
        end = start + friend['duration']
        if end <= friend['end']:
            candidates.append((end, start, friend))
    if not candidates:
        break
    # Select friend with earliest end time
    earliest = min(candidates, key=lambda x: x[0])
    end_time, start_time, selected = earliest
    itinerary.append({
        'action': 'meet',
        'location': selected['location'],
        'person': selected['name'],
        'start_time': minutes_to_time(start_time),
        'end_time': minutes_to_time(end_time)
    })
    current_time = end_time
    current_location = selected['location']
    remaining.remove(selected)

print(json.dumps({'itinerary': itinerary}, indent=2))