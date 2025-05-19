import heapq
import json

def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

friends = [
    {'name': 'Jeffrey', 'location': 'Fisherman\'s Wharf', 'start': 615, 'end': 780, 'duration': 90, 'index': 0},
    {'name': 'Ronald', 'location': 'Alamo Square', 'start': 465, 'end': 885, 'duration': 120, 'index': 1},
    {'name': 'Jason', 'location': 'Financial District', 'start': 645, 'end': 960, 'duration': 105, 'index': 2},
    {'name': 'Melissa', 'location': 'Union Square', 'start': 1065, 'end': 1095, 'duration': 15, 'index': 3},
    {'name': 'Elizabeth', 'location': 'Sunset District', 'start': 885, 'end': 1050, 'duration': 105, 'index': 4},
    {'name': 'Margaret', 'location': 'Embarcadero', 'start': 795, 'end': 1140, 'duration': 90, 'index': 5},
    {'name': 'George', 'location': 'Golden Gate Park', 'start': 1140, 'end': 1320, 'duration': 75, 'index': 6},
    {'name': 'Richard', 'location': 'Chinatown', 'start': 570, 'end': 1260, 'duration': 15, 'index': 7},
    {'name': 'Laura', 'location': 'Richmond District', 'start': 585, 'end': 1080, 'duration': 60, 'index': 8},
]

travel_time = {
    ('Presidio', 'Fisherman\'s Wharf'): 19,
    ('Presidio', 'Alamo Square'): 19,
    ('Presidio', 'Financial District'): 23,
    ('Presidio', 'Union Square'): 22,
    ('Presidio', 'Sunset District'): 15,
    ('Presidio', 'Embarcadero'): 20,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Chinatown'): 21,
    ('Presidio', 'Richmond District'): 7,
    ('Fisherman\'s Wharf', 'Presidio'): 17,
    ('Fisherman\'s Wharf', 'Alamo Square'): 21,
    ('Fisherman\'s Wharf', 'Financial District'): 11,
    ('Fisherman\'s Wharf', 'Union Square'): 13,
    ('Fisherman\'s Wharf', 'Sunset District'): 27,
    ('Fisherman\'s Wharf', 'Embarcadero'): 8,
    ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
    ('Fisherman\'s Wharf', 'Chinatown'): 12,
    ('Fisherman\'s Wharf', 'Richmond District'): 18,
    ('Alamo Square', 'Presidio'): 17,
    ('Alamo Square', 'Fisherman\'s Wharf'): 19,
    ('Alamo Square', 'Financial District'): 17,
    ('Alamo Square', 'Union Square'): 14,
    ('Alamo Square', 'Sunset District'): 16,
    ('Alamo Square', 'Embarcadero'): 16,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Alamo Square', 'Chinatown'): 15,
    ('Alamo Square', 'Richmond District'): 11,
    ('Financial District', 'Presidio'): 22,
    ('Financial District', 'Fisherman\'s Wharf'): 10,
    ('Financial District', 'Alamo Square'): 17,
    ('Financial District', 'Union Square'): 9,
    ('Financial District', 'Sunset District'): 30,
    ('Financial District', 'Embarcadero'): 4,
    ('Financial District', 'Golden Gate Park'): 23,
    ('Financial District', 'Chinatown'): 5,
    ('Financial District', 'Richmond District'): 21,
    ('Union Square', 'Presidio'): 24,
    ('Union Square', 'Fisherman\'s Wharf'): 15,
    ('Union Square', 'Alamo Square'): 15,
    ('Union Square', 'Financial District'): 9,
    ('Union Square', 'Sunset District'): 27,
    ('Union Square', 'Embarcadero'): 11,
    ('Union Square', 'Golden Gate Park'): 22,
    ('Union Square', 'Chinatown'): 7,
    ('Union Square', 'Richmond District'): 20,
    ('Sunset District', 'Presidio'): 16,
    ('Sunset District', 'Fisherman\'s Wharf'): 29,
    ('Sunset District', 'Alamo Square'): 17,
    ('Sunset District', 'Financial District'): 30,
    ('Sunset District', 'Union Square'): 30,
    ('Sunset District', 'Embarcadero'): 30,
    ('Sunset District', 'Golden Gate Park'): 11,
    ('Sunset District', 'Chinatown'): 30,
    ('Sunset District', 'Richmond District'): 12,
    ('Embarcadero', 'Presidio'): 20,
    ('Embarcadero', 'Fisherman\'s Wharf'): 6,
    ('Embarcadero', 'Alamo Square'): 19,
    ('Embarcadero', 'Financial District'): 5,
    ('Embarcadero', 'Union Square'): 10,
    ('Embarcadero', 'Sunset District'): 30,
    ('Embarcadero', 'Golden Gate Park'): 25,
    ('Embarcadero', 'Chinatown'): 7,
    ('Embarcadero', 'Richmond District'): 21,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
    ('Golden Gate Park', 'Alamo Square'): 9,
    ('Golden Gate Park', 'Financial District'): 26,
    ('Golden Gate Park', 'Union Square'): 22,
    ('Golden Gate Park', 'Sunset District'): 10,
    ('Golden Gate Park', 'Embarcadero'): 25,
    ('Golden Gate Park', 'Chinatown'): 23,
    ('Golden Gate Park', 'Richmond District'): 7,
    ('Chinatown', 'Presidio'): 19,
    ('Chinatown', 'Fisherman\'s Wharf'): 8,
    ('Chinatown', 'Alamo Square'): 17,
    ('Chinatown', 'Financial District'): 5,
    ('Chinatown', 'Union Square'): 7,
    ('Chinatown', 'Sunset District'): 29,
    ('Chinatown', 'Embarcadero'): 5,
    ('Chinatown', 'Golden Gate Park'): 23,
    ('Chinatown', 'Richmond District'): 20,
    ('Richmond District', 'Presidio'): 7,
    ('Richmond District', 'Fisherman\'s Wharf'): 18,
    ('Richmond District', 'Alamo Square'): 13,
    ('Richmond District', 'Financial District'): 22,
    ('Richmond District', 'Union Square'): 21,
    ('Richmond District', 'Sunset District'): 11,
    ('Richmond District', 'Embarcadero'): 19,
    ('Richmond District', 'Golden Gate Park'): 9,
    ('Richmond District', 'Chinatown'): 20,
}

heap = []
dp = {}
best_count = 0
best_schedule = []

heapq.heappush(heap, ((-0, 540, 540, 'Presidio', 0, []))
dp[('Presidio', 0)] = 540

while heap:
    priority, current_priority_time, current_time, current_location, mask, schedule = heapq.heappop(heap)
    num_friends = -priority

    if (current_location, mask) in dp and dp[(current_location, mask)] < current_time:
        continue

    if num_friends > best_count or (num_friends == best_count and current_time < (int(best_schedule[-1]['end_time'].split(':')[0]) * 60 + int(best_schedule[-1]['end_time'].split(':')[1]) if best_schedule else 0)):
        best_count = num_friends
        best_schedule = schedule.copy()

    for friend in friends:
        if not (mask & (1 << friend['index'])):
            from_loc = current_location
            to_loc = friend['location']
            tt = travel_time.get((from_loc, to_loc))
            if tt is None:
                continue
            arrival_time = current_time + tt
            start_time = max(arrival_time, friend['start'])
            end_time = start_time + friend['duration']
            if end_time > friend['end']:
                continue
            new_mask = mask | (1 << friend['index'])
            new_schedule = schedule.copy()
            new_schedule.append({
                'action': 'meet',
                'location': to_loc,
                'person': friend['name'],
                'start_time': minutes_to_time(start_time),
                'end_time': minutes_to_time(end_time)
            })
            new_key = (to_loc, new_mask)
            if new_key not in dp or end_time < dp.get(new_key, float('inf')):
                dp[new_key] = end_time
                heapq.heappush(heap, ((-num_friends - 1, end_time, end_time, to_loc, new_mask, new_schedule)))

output = {"itinerary": best_schedule}
print(json.dumps(output))