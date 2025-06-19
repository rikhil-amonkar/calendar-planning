import collections
import json

def parse_time(s):
    s = s.strip().upper()
    if s.endswith('AM') or s.endswith('PM'):
        meridian = s[-2:]
        s = s[:-2].strip()
    else:
        meridian = None
    parts = s.split(':')
    hour = int(parts[0])
    minute = int(parts[1])
    if meridian == 'PM' and hour != 12:
        hour += 12
    elif meridian == 'AM' and hour == 12:
        hour = 0
    return hour * 60 + minute

def minutes_to_time(m):
    hour = m // 60
    minute = m % 60
    if hour == 0:
        return f"12:{minute:02d} AM"
    elif hour < 12:
        return f"{hour}:{minute:02d} AM"
    elif hour == 12:
        return f"12:{minute:02d} PM"
    else:
        return f"{hour - 12}:{minute:02d} PM"

travel_data = [
    ("Pacific Heights", "Marina District", 6),
    ("Pacific Heights", "The Castro", 16),
    ("Pacific Heights", "Richmond District", 12),
    ("Pacific Heights", "Alamo Square", 10),
    ("Pacific Heights", "Financial District", 13),
    ("Pacific Heights", "Presidio", 11),
    ("Pacific Heights", "Mission District", 15),
    ("Pacific Heights", "Nob Hill", 8),
    ("Pacific Heights", "Russian Hill", 7),
    ("Marina District", "Pacific Heights", 7),
    ("Marina District", "The Castro", 22),
    ("Marina District", "Richmond District", 11),
    ("Marina District", "Alamo Square", 15),
    ("Marina District", "Financial District", 17),
    ("Marina District", "Presidio", 10),
    ("Marina District", "Mission District", 20),
    ("Marina District", "Nob Hill", 12),
    ("Marina District", "Russian Hill", 8),
    ("The Castro", "Pacific Heights", 16),
    ("The Castro", "Marina District", 21),
    ("The Castro", "Richmond District", 16),
    ("The Castro", "Alamo Square", 8),
    ("The Castro", "Financial District", 21),
    ("The Castro", "Presidio", 20),
    ("The Castro", "Mission District", 7),
    ("The Castro", "Nob Hill", 16),
    ("The Castro", "Russian Hill", 18),
    ("Richmond District", "Pacific Heights", 10),
    ("Richmond District", "Marina District", 9),
    ("Richmond District", "The Castro", 16),
    ("Richmond District", "Alamo Square", 13),
    ("Richmond District", "Financial District", 22),
    ("Richmond District", "Presidio", 7),
    ("Richmond District", "Mission District", 20),
    ("Richmond District", "Nob Hill", 17),
    ("Richmond District", "Russian Hill", 13),
    ("Alamo Square", "Pacific Heights", 10),
    ("Alamo Square", "Marina District", 15),
    ("Alamo Square", "The Castro", 8),
    ("Alamo Square", "Richmond District", 11),
    ("Alamo Square", "Financial District", 17),
    ("Alamo Square", "Presidio", 17),
    ("Alamo Square", "Mission District", 10),
    ("Alamo Square", "Nob Hill", 11),
    ("Alamo Square", "Russian Hill", 13),
    ("Financial District", "Pacific Heights", 13),
    ("Financial District", "Marina District", 15),
    ("Financial District", "The Castro", 20),
    ("Financial District", "Richmond District", 21),
    ("Financial District", "Alamo Square", 17),
    ("Financial District", "Presidio", 22),
    ("Financial District", "Mission District", 17),
    ("Financial District", "Nob Hill", 8),
    ("Financial District", "Russian Hill", 11),
    ("Presidio", "Pacific Heights", 11),
    ("Presidio", "Marina District", 11),
    ("Presidio", "The Castro", 21),
    ("Presidio", "Richmond District", 7),
    ("Presidio", "Alamo Square", 19),
    ("Presidio", "Financial District", 23),
    ("Presidio", "Mission District", 26),
    ("Presidio", "Nob Hill", 18),
    ("Presidio", "Russian Hill", 14),
    ("Mission District", "Pacific Heights", 16),
    ("Mission District", "Marina District", 19),
    ("Mission District", "The Castro", 7),
    ("Mission District", "Richmond District", 20),
    ("Mission District", "Alamo Square", 11),
    ("Mission District", "Financial District", 15),
    ("Mission District", "Presidio", 25),
    ("Mission District", "Nob Hill", 12),
    ("Mission District", "Russian Hill", 15),
    ("Nob Hill", "Pacific Heights", 8),
    ("Nob Hill", "Marina District", 11),
    ("Nob Hill", "The Castro", 17),
    ("Nob Hill", "Richmond District", 14),
    ("Nob Hill", "Alamo Square", 11),
    ("Nob Hill", "Financial District", 9),
    ("Nob Hill", "Presidio", 17),
    ("Nob Hill", "Mission District", 13),
    ("Nob Hill", "Russian Hill", 5),
    ("Russian Hill", "Pacific Heights", 7),
    ("Russian Hill", "Marina District", 7),
    ("Russian Hill", "The Castro", 21),
    ("Russian Hill", "Richmond District", 14),
    ("Russian Hill", "Alamo Square", 15),
    ("Russian Hill", "Financial District", 11),
    ("Russian Hill", "Presidio", 14),
    ("Russian Hill", "Mission District", 16),
    ("Russian Hill", "Nob Hill", 5)
]

travel_times = {}
for from_loc, to_loc, t in travel_data:
    if from_loc not in travel_times:
        travel_times[from_loc] = {}
    travel_times[from_loc][to_loc] = t

friends = [
    {'name': 'Linda', 'location': 'Marina District', 'start': parse_time('6:00PM'), 'end': parse_time('10:00PM'), 'duration': 30},
    {'name': 'Kenneth', 'location': 'The Castro', 'start': parse_time('2:45PM'), 'end': parse_time('4:15PM'), 'duration': 30},
    {'name': 'Kimberly', 'location': 'Richmond District', 'start': parse_time('2:15PM'), 'end': parse_time('10:00PM'), 'duration': 30},
    {'name': 'Paul', 'location': 'Alamo Square', 'start': parse_time('9:00PM'), 'end': parse_time('9:30PM'), 'duration': 15},
    {'name': 'Carol', 'location': 'Financial District', 'start': parse_time('10:15AM'), 'end': parse_time('12:00PM'), 'duration': 60},
    {'name': 'Brian', 'location': 'Presidio', 'start': parse_time('10:00AM'), 'end': parse_time('9:30PM'), 'duration': 75},
    {'name': 'Laura', 'location': 'Mission District', 'start': parse_time('4:15PM'), 'end': parse_time('8:30PM'), 'duration': 30},
    {'name': 'Sandra', 'location': 'Nob Hill', 'start': parse_time('9:15AM'), 'end': parse_time('6:30PM'), 'duration': 60},
    {'name': 'Karen', 'location': 'Russian Hill', 'start': parse_time('6:30PM'), 'end': parse_time('10:00PM'), 'duration': 75}
]

dp = {}
parent = {}
start_mask = 0
start_loc = 'Pacific Heights'
start_time_val = parse_time('9:00AM')
dp[(start_mask, start_loc)] = start_time_val
parent[(start_mask, start_loc)] = None

states_by_count = collections.defaultdict(list)
states_by_count[0].append((start_mask, start_loc, start_time_val))

for count in range(0, 9):
    for state in states_by_count[count]:
        mask, loc, time_val = state
        if (mask, loc) in dp and dp[(mask, loc)] < time_val:
            continue
        for i in range(len(friends)):
            if mask & (1 << i):
                continue
            friend = friends[i]
            to_loc = friend['location']
            if loc in travel_times and to_loc in travel_times[loc]:
                travel_time = travel_times[loc][to_loc]
            else:
                continue
            arrival_time = time_val + travel_time
            start_meeting = max(arrival_time, friend['start'])
            end_meeting = start_meeting + friend['duration']
            if end_meeting > friend['end']:
                continue
            new_mask = mask | (1 << i)
            new_loc = to_loc
            if (new_mask, new_loc) not in dp or end_meeting < dp.get((new_mask, new_loc), float('inf')):
                dp[(new_mask, new_loc)] = end_meeting
                parent[(new_mask, new_loc)] = (mask, loc, i, start_meeting, end_meeting)
                states_by_count[count+1].append((new_mask, new_loc, end_meeting))

best_state = None
best_count = -1
best_time = float('inf')
for key, end_time in dp.items():
    mask, loc = key
    count = bin(mask).count('1')
    if count > best_count or (count == best_count and end_time < best_time):
        best_count = count
        best_time = end_time
        best_state = key

itinerary = []
current_state = best_state
while current_state in parent and parent[current_state] is not None:
    mask, loc = current_state
    prev_mask, prev_loc, i, start_meeting, end_meeting = parent[current_state]
    friend = friends[i]
    itinerary.append({
        'action': 'meet',
        'location': friend['location'],
        'person': friend['name'],
        'start_time': minutes_to_time(start_meeting),
        'end_time': minutes_to_time(end_meeting)
    })
    current_state = (prev_mask, prev_loc)

itinerary.reverse()
result = {
    "itinerary": itinerary
}
print(json.dumps(result))