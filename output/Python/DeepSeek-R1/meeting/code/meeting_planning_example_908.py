import json

def time_to_min(t_str):
    time_part, period = t_str[:-2], t_str[-2:]
    hours, minutes = map(int, time_part.split(':'))
    if period == 'PM':
        if hours != 12:
            hours += 12
    elif period == 'AM' and hours == 12:
        hours = 0
    return hours * 60 + minutes

def min_to_time(m):
    hours = m // 60
    mins = m % 60
    return f"{hours}:{mins:02d}" if mins != 0 else f"{hours}:00"

travel_times = {
    'Financial District': {'Fisherman\'s Wharf': 10, 'Presidio': 22, 'Bayview': 19, 'Haight-Ashbury': 19, 'Russian Hill': 11, 'The Castro': 20, 'Marina District': 15, 'Richmond District': 21, 'Union Square': 9, 'Sunset District': 30},
    'Fisherman\'s Wharf': {'Financial District': 11, 'Presidio': 17, 'Bayview': 26, 'Haight-Ashbury': 22, 'Russian Hill': 7, 'The Castro': 27, 'Marina District': 9, 'Richmond District': 18, 'Union Square': 13, 'Sunset District': 27},
    'Presidio': {'Financial District': 23, 'Fisherman\'s Wharf': 19, 'Bayview': 31, 'Haight-Ashbury': 15, 'Russian Hill': 14, 'The Castro': 21, 'Marina District': 11, 'Richmond District': 7, 'Union Square': 22, 'Sunset District': 15},
    'Bayview': {'Financial District': 19, 'Fisherman\'s Wharf': 25, 'Presidio': 32, 'Haight-Ashbury': 19, 'Russian Hill': 23, 'The Castro': 19, 'Marina District': 27, 'Richmond District': 25, 'Union Square': 18, 'Sunset District': 23},
    'Haight-Ashbury': {'Financial District': 21, 'Fisherman\'s Wharf': 23, 'Presidio': 15, 'Bayview': 18, 'Russian Hill': 17, 'The Castro': 6, 'Marina District': 17, 'Richmond District': 10, 'Union Square': 19, 'Sunset District': 15},
    'Russian Hill': {'Financial District': 11, 'Fisherman\'s Wharf': 7, 'Presidio': 14, 'Bayview': 23, 'Haight-Ashbury': 17, 'The Castro': 21, 'Marina District': 7, 'Richmond District': 14, 'Union Square': 10, 'Sunset District': 23},
    'The Castro': {'Financial District': 21, 'Fisherman\'s Wharf': 24, 'Presidio': 20, 'Bayview': 19, 'Haight-Ashbury': 6, 'Russian Hill': 18, 'Marina District': 21, 'Richmond District': 16, 'Union Square': 19, 'Sunset District': 17},
    'Marina District': {'Financial District': 17, 'Fisherman\'s Wharf': 10, 'Presidio': 10, 'Bayview': 27, 'Haight-Ashbury': 16, 'Russian Hill': 8, 'The Castro': 22, 'Richmond District': 11, 'Union Square': 16, 'Sunset District': 19},
    'Richmond District': {'Financial District': 22, 'Fisherman\'s Wharf': 18, 'Presidio': 7, 'Bayview': 27, 'Haight-Ashbury': 10, 'Russian Hill': 13, 'The Castro': 16, 'Marina District': 9, 'Union Square': 21, 'Sunset District': 11},
    'Union Square': {'Financial District': 9, 'Fisherman\'s Wharf': 15, 'Presidio': 24, 'Bayview': 15, 'Haight-Ashbury': 18, 'Russian Hill': 13, 'The Castro': 17, 'Marina District': 18, 'Richmond District': 20, 'Sunset District': 27},
    'Sunset District': {'Financial District': 30, 'Fisherman\'s Wharf': 29, 'Presidio': 16, 'Bayview': 22, 'Haight-Ashbury': 15, 'Russian Hill': 24, 'The Castro': 17, 'Marina District': 21, 'Richmond District': 12, 'Union Square': 30}
}

friends = [
    {'name': 'Mark', 'location': 'Fisherman\'s Wharf', 'start': time_to_min('8:15AM'), 'end': time_to_min('10:00AM'), 'duration': 30},
    {'name': 'Stephanie', 'location': 'Presidio', 'start': time_to_min('12:15PM'), 'end': time_to_min('3:00PM'), 'duration': 75},
    {'name': 'Betty', 'location': 'Bayview', 'start': time_to_min('7:15AM'), 'end': time_to_min('8:30PM'), 'duration': 15},
    {'name': 'Lisa', 'location': 'Haight-Ashbury', 'start': time_to_min('3:30PM'), 'end': time_to_min('6:30PM'), 'duration': 45},
    {'name': 'William', 'location': 'Russian Hill', 'start': time_to_min('6:45PM'), 'end': time_to_min('8:00PM'), 'duration': 60},
    {'name': 'Brian', 'location': 'The Castro', 'start': time_to_min('9:15AM'), 'end': time_to_min('1:15PM'), 'duration': 30},
    {'name': 'Joseph', 'location': 'Marina District', 'start': time_to_min('10:45AM'), 'end': time_to_min('3:00PM'), 'duration': 90},
    {'name': 'Ashley', 'location': 'Richmond District', 'start': time_to_min('9:45AM'), 'end': time_to_min('11:15AM'), 'duration': 45},
    {'name': 'Patricia', 'location': 'Union Square', 'start': time_to_min('4:30PM'), 'end': time_to_min('8:00PM'), 'duration': 120},
    {'name': 'Karen', 'location': 'Sunset District', 'start': time_to_min('4:30PM'), 'end': time_to_min('10:00PM'), 'duration': 105}
]

friends_sorted = sorted(friends, key=lambda x: x['end'])

current_time = time_to_min('9:00AM')
current_location = 'Financial District'
itinerary = []

for friend in friends_sorted:
    loc = friend['location']
    start = friend['start']
    end = friend['end']
    duration = friend['duration']
    name = friend['name']
    
    if current_location not in travel_times or loc not in travel_times[current_location]:
        continue
    travel_time = travel_times[current_location][loc]
    
    earliest_start = max(start, current_time + travel_time)
    if earliest_start + duration > end:
        continue
    
    itinerary.append({
        'action': 'meet',
        'location': loc,
        'person': name,
        'start_time': min_to_time(earliest_start).replace(":00", "").replace(":0", ":") if mins == 0 else min_to_time(earliest_start).lstrip("0"),
        'end_time': min_to_time(earliest_start + duration).replace(":00", "").replace(":0", ":") if (earliest_start + duration) % 60 == 0 else min_to_time(earliest_start + duration).lstrip("0")
    })
    
    current_time = earliest_start + duration
    current_location = loc

print(json.dumps({'itinerary': itinerary}, indent=2))