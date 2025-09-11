import itertools
import json

def time_to_minutes(s):
    s = s.strip().upper()
    if s.endswith('AM'):
        s = s[:-2].strip()
        parts = s.split(':')
        h = int(parts[0])
        m = int(parts[1])
        if h == 12:
            h = 0
        return h * 60 + m
    else:
        s = s[:-2].strip()
        parts = s.split(':')
        h = int(parts[0])
        m = int(parts[1])
        if h != 12:
            h += 12
        return h * 60 + m

def minutes_to_time(m):
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

travel_times = {
    'Union Square': {
        'The Castro': 17, 'North Beach': 10, 'Embarcadero': 11, 'Alamo Square': 15,
        'Nob Hill': 9, 'Presidio': 24, 'Fisherman\'s Wharf': 15, 'Mission District': 14,
        'Haight-Ashbury': 18
    },
    'The Castro': {
        'Union Square': 19, 'North Beach': 20, 'Embarcadero': 22, 'Alamo Square': 8,
        'Nob Hill': 16, 'Presidio': 20, 'Fisherman\'s Wharf': 24, 'Mission District': 7,
        'Haight-Ashbury': 6
    },
    'North Beach': {
        'Union Square': 7, 'The Castro': 23, 'Embarcadero': 6, 'Alamo Square': 16,
        'Nob Hill': 7, 'Presidio': 17, 'Fisherman\'s Wharf': 5, 'Mission District': 18,
        'Haight-Ashbury': 18
    },
    'Embarcadero': {
        'Union Square': 10, 'The Castro': 25, 'North Beach': 5, 'Alamo Square': 19,
        'Nob Hill': 10, 'Presidio': 20, 'Fisherman\'s Wharf': 6, 'Mission District': 20,
        'Haight-Ashbury': 21
    },
    'Alamo Square': {
        'Union Square': 14, 'The Castro': 8, 'North Beach': 15, 'Embarcadero': 16,
        'Nob Hill': 11, 'Presidio': 17, 'Fisherman\'s Wharf': 19, 'Mission District': 10,
        'Haight-Ashbury': 5
    },
    'Nob Hill': {
        'Union Square': 7, 'The Castro': 17, 'North Beach': 8, 'Embarcadero': 9,
        'Alamo Square': 11, 'Presidio': 17, 'Fisherman\'s Wharf': 10, 'Mission District': 13,
        'Haight-Ashbury': 13
    },
    'Presidio': {
        'Union Square': 22, 'The Castro': 21, 'North Beach': 18, 'Embarcadero': 20,
        'Alamo Square': 19, 'Nob Hill': 18, 'Fisherman\'s Wharf': 19, 'Mission District': 26,
        'Haight-Ashbury': 15
    },
    'Fisherman\'s Wharf': {
        'Union Square': 13, 'The Castro': 27, 'North Beach': 6, 'Embarcadero': 8,
        'Alamo Square': 21, 'Nob Hill': 11, 'Presidio': 17, 'Mission District': 22,
        'Haight-Ashbury': 22
    },
    'Mission District': {
        'Union Square': 15, 'The Castro': 7, 'North Beach': 17, 'Embarcadero': 19,
        'Alamo Square': 11, 'Nob Hill': 12, 'Presidio': 25, 'Fisherman\'s Wharf': 22,
        'Haight-Ashbury': 12
    },
    'Haight-Ashbury': {
        'Union Square': 19, 'The Castro': 6, 'North Beach': 19, 'Embarcadero': 20,
        'Alamo Square': 5, 'Nob Hill': 15, 'Presidio': 15, 'Fisherman\'s Wharf': 23,
        'Mission District': 11
    }
}

meetings = [
    {'person': 'Melissa', 'location': 'The Castro', 'start_avail': time_to_minutes('8:15PM'), 'end_avail': time_to_minutes('9:15PM'), 'min_duration': 30, 'fixed': False},
    {'person': 'Kimberly', 'location': 'North Beach', 'start_avail': time_to_minutes('7:00AM'), 'end_avail': time_to_minutes('10:30AM'), 'min_duration': 15, 'fixed': False},
    {'person': 'Joseph', 'location': 'Embarcadero', 'start_avail': time_to_minutes('3:30PM'), 'end_avail': time_to_minutes('7:30PM'), 'min_duration': 75, 'fixed': False},
    {'person': 'Barbara', 'location': 'Alamo Square', 'start_avail': time_to_minutes('8:45PM'), 'end_avail': time_to_minutes('9:45PM'), 'min_duration': 15, 'fixed': False},
    {'person': 'Kenneth', 'location': 'Nob Hill', 'start_avail': time_to_minutes('12:15PM'), 'end_avail': time_to_minutes('5:15PM'), 'min_duration': 105, 'fixed': False},
    {'person': 'Joshua', 'location': 'Presidio', 'start_avail': time_to_minutes('4:30PM'), 'end_avail': time_to_minutes('6:15PM'), 'min_duration': 105, 'fixed': True},
    {'person': 'Brian', 'location': 'Fisherman\'s Wharf', 'start_avail': time_to_minutes('9:30AM'), 'end_avail': time_to_minutes('3:30PM'), 'min_duration': 45, 'fixed': False},
    {'person': 'Steven', 'location': 'Mission District', 'start_avail': time_to_minutes('7:30PM'), 'end_avail': time_to_minutes('9:00PM'), 'min_duration': 90, 'fixed': True},
    {'person': 'Betty', 'location': 'Haight-Ashbury', 'start_avail': time_to_minutes('7:00PM'), 'end_avail': time_to_minutes('8:30PM'), 'min_duration': 90, 'fixed': True}
]

start_time = time_to_minutes('9:00AM')
start_location = 'Union Square'

best_count = 0
best_schedule = None

for perm in itertools.permutations(meetings):
    current_time = start_time
    current_loc = start_location
    schedule = []
    count = 0
    feasible = True
    for meeting in perm:
        loc = meeting['location']
        travel_time = travel_times[current_loc][loc]
        arrival = current_time + travel_time
        if meeting['fixed']:
            if arrival > meeting['start_avail']:
                feasible = False
                break
            start = meeting['start_avail']
            end = meeting['end_avail']
            current_time = end
            current_loc = loc
            schedule.append({
                'action': 'meet',
                'location': loc,
                'person': meeting['person'],
                'start_time': minutes_to_time(start),
                'end_time': minutes_to_time(end)
            })
            count += 1
        else:
            start = max(arrival, meeting['start_avail'])
            if start + meeting['min_duration'] > meeting['end_avail']:
                feasible = False
                break
            end = start + meeting['min_duration']
            current_time = end
            current_loc = loc
            schedule.append({
                'action': 'meet',
                'location': loc,
                'person': meeting['person'],
                'start_time': minutes_to_time(start),
                'end_time': minutes_to_time(end)
            })
            count += 1
    if feasible and count > best_count:
        best_count = count
        best_schedule = schedule

if best_schedule is None:
    best_schedule = []

output = {"itinerary": best_schedule}
print(json.dumps(output, indent=2))