import itertools
import json

def parse_time(time_str):
    time_str = time_str.strip().upper()
    if time_str.endswith(('AM', 'PM')):
        time_part, period = time_str[:-2], time_str[-2:]
        hours, minutes = map(int, time_part.split(':'))
        if period == 'PM' and hours != 12:
            hours += 12
        elif period == 'AM' and hours == 12:
            hours = 0
        return hours * 60 + minutes
    else:
        hours, minutes = map(int, time_str.split(':'))
        return hours * 60 + minutes

def format_time(mins):
    h, m = divmod(mins, 60)
    return f"{h}:{m:02d}".replace(":00", ":0").replace(":0", ":")

travel_times = {
    'Union Square': {'Nob Hill': 9, 'Haight-Ashbury': 18, 'Chinatown': 7, 'Marina District': 18},
    'Nob Hill': {'Union Square': 7, 'Haight-Ashbury': 13, 'Chinatown': 6, 'Marina District': 11},
    'Haight-Ashbury': {'Union Square': 17, 'Nob Hill': 15, 'Chinatown': 19, 'Marina District': 17},
    'Chinatown': {'Union Square': 7, 'Nob Hill': 8, 'Haight-Ashbury': 19, 'Marina District': 12},
    'Marina District': {'Union Square': 16, 'Nob Hill': 12, 'Haight-Ashbury': 16, 'Chinatown': 16}
}

friends = [
    {'name':'Karen', 'location':'Nob Hill', 'start':parse_time('9:15PM'), 'end':parse_time('9:45PM'), 'duration':30},
    {'name':'Joseph', 'location':'Haight-Ashbury', 'start':parse_time('12:30PM'), 'end':parse_time('7:45PM'), 'duration':90},
    {'name':'Sandra', 'location':'Chinatown', 'start':parse_time('7:15AM'), 'end':parse_time('7:15PM'), 'duration':75},
    {'name':'Nancy', 'location':'Marina District', 'start':parse_time('11:00AM'), 'end':parse_time('8:15PM'), 'duration':105}
]

karen = friends[0]
others = friends[1:]

best = []
max_people = 0

for perm in itertools.permutations(others):
    schedule = []
    current = 540
    loc = 'Union Square'
    valid = True
    
    for p in perm:
        travel = travel_times[loc][p['location']]
        arrive = current + travel
        start = max(arrive, p['start'])
        end = start + p['duration']
        if end > p['end']:
            valid = False
            break
        schedule.append((p['name'], p['location'], start, end))
        current = end
        loc = p['location']
    
    if valid:
        travel_k = travel_times[loc][karen['location']]
        arrive_k = current + travel_k
        k_start = karen['start']
        if arrive_k <= k_start and (k_start + karen['duration']) <= karen['end']:
            total = len(perm) + 1
            temp = schedule + [('Karen', 'Nob Hill', k_start, k_start +30)]
        else:
            total = len(perm)
            temp = schedule
        
        if total > max_people or (total == max_people and current < current):
            max_people = total
            best = temp

formatted = []
for entry in best:
    name, loc, s, e = entry
    formatted.append({
        "action": "meet",
        "location": loc,
        "person": name,
        "start_time": format_time(s).replace(':0',':'),
        "end_time": format_time(e).replace(':0',':')
    })

print(json.dumps({"itinerary": formatted}, indent=2))