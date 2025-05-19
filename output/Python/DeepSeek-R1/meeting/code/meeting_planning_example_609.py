import itertools
import json

friends = [
    {'name': 'David', 'location': 'Mission District', 'start': 480, 'end': 1185, 'duration':45},
    {'name': 'Kenneth', 'location': 'Alamo Square', 'start': 840, 'end': 1185, 'duration':120},
    {'name': 'John', 'location': 'Pacific Heights', 'start': 1020, 'end': 1200, 'duration':15},
    {'name': 'Charles', 'location': 'Union Square', 'start': 1305, 'end': 1365, 'duration':60},
    {'name': 'Deborah', 'location': 'Golden Gate Park', 'start': 420, 'end': 1095, 'duration':90},
    {'name': 'Karen', 'location': 'Sunset District', 'start': 1065, 'end': 1275, 'duration':15}
]

travel_time = {
    ('Chinatown', 'Mission District'): 18,
    ('Chinatown', 'Alamo Square'): 17,
    ('Chinatown', 'Pacific Heights'): 10,
    ('Chinatown', 'Union Square'): 7,
    ('Chinatown', 'Golden Gate Park'): 23,
    ('Chinatown', 'Sunset District'): 29,
    ('Mission District', 'Chinatown'): 16,
    ('Mission District', 'Alamo Square'): 11,
    ('Mission District', 'Pacific Heights'): 16,
    ('Mission District', 'Union Square'): 15,
    ('Mission District', 'Golden Gate Park'): 17,
    ('Mission District', 'Sunset District'): 24,
    ('Alamo Square', 'Chinatown'): 16,
    ('Alamo Square', 'Mission District'): 10,
    ('Alamo Square', 'Pacific Heights'): 10,
    ('Alamo Square', 'Union Square'): 14,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Alamo Square', 'Sunset District'): 16,
    ('Pacific Heights', 'Chinatown'): 11,
    ('Pacific Heights', 'Mission District'): 15,
    ('Pacific Heights', 'Alamo Square'): 10,
    ('Pacific Heights', 'Union Square'): 12,
    ('Pacific Heights', 'Golden Gate Park'): 15,
    ('Pacific Heights', 'Sunset District'): 21,
    ('Union Square', 'Chinatown'): 7,
    ('Union Square', 'Mission District'): 14,
    ('Union Square', 'Alamo Square'): 15,
    ('Union Square', 'Pacific Heights'): 15,
    ('Union Square', 'Golden Gate Park'): 22,
    ('Union Square', 'Sunset District'): 26,
    ('Golden Gate Park', 'Chinatown'): 23,
    ('Golden Gate Park', 'Mission District'): 17,
    ('Golden Gate Park', 'Alamo Square'): 10,
    ('Golden Gate Park', 'Pacific Heights'): 16,
    ('Golden Gate Park', 'Union Square'): 22,
    ('Golden Gate Park', 'Sunset District'): 10,
    ('Sunset District', 'Chinatown'): 30,
    ('Sunset District', 'Mission District'): 24,
    ('Sunset District', 'Alamo Square'): 17,
    ('Sunset District', 'Pacific Heights'): 21,
    ('Sunset District', 'Union Square'): 30,
    ('Sunset District', 'Golden Gate Park'): 11
}

best_count = 0
best_end = float('inf')
best_itinerary = []

for perm in itertools.permutations(friends):
    current_time = 540  # 9:00 AM
    current_loc = 'Chinatown'
    itinerary = []
    count = 0
    
    for friend in perm:
        key = (current_loc, friend['location'])
        if key not in travel_time:
            break
        arrive = current_time + travel_time[key]
        start = max(arrive, friend['start'])
        if start + friend['duration'] > friend['end']:
            continue
        end = start + friend['duration']
        itinerary.append((friend['name'], friend['location'], start, end))
        current_time = end
        current_loc = friend['location']
        count += 1
    
    if count > best_count or (count == best_count and current_time < best_end):
        best_count = count
        best_end = current_time
        best_itinerary = itinerary.copy()

formatted = []
for item in best_itinerary:
    name, loc, start, end = item
    sh = start // 60
    sm = start % 60
    eh = end // 60
    em = end % 60
    start_str = f"{sh}:{sm:02d}"
    end_str = f"{eh}:{em:02d}"
    formatted.append({
        "action": "meet",
        "location": loc,
        "person": name,
        "start_time": start_str,
        "end_time": end_str
    })

print(json.dumps({"itinerary": formatted}, indent=2))