import heapq
import json

def time_to_minutes(timestr):
    time_format = '%I:%M%p'
    dt = datetime.strptime(timestr, time_format)
    return dt.hour * 60 + dt.minute

def minutes_to_time(mins):
    hours = mins // 60
    minutes = mins % 60
    return f"{hours}:{minutes:02}"

friends = [
    {'name': 'Amanda', 'location': 'Marina District', 'start': 885, 'end': 1170, 'duration': 105},
    {'name': 'Melissa', 'location': 'The Castro', 'start': 570, 'end': 1020, 'duration': 30},
    {'name': 'Jeffrey', 'location': 'Fisherman\'s Wharf', 'start': 765, 'end': 1170, 'duration': 120},
    {'name': 'Matthew', 'location': 'Bayview', 'start': 615, 'end': 795, 'duration': 30},
    {'name': 'Nancy', 'location': 'Pacific Heights', 'start': 1020, 'end': 1290, 'duration': 105},
    {'name': 'Karen', 'location': 'Mission District', 'start': 1050, 'end': 1230, 'duration': 105},
    {'name': 'Robert', 'location': 'Alamo Square', 'start': 675, 'end': 1050, 'duration': 120},
    {'name': 'Joseph', 'location': 'Golden Gate Park', 'start': 510, 'end': 1275, 'duration': 105}
]

travel_time = {
    'Presidio': {'Marina District': 11, 'The Castro': 21, 'Fisherman\'s Wharf': 19, 'Bayview': 31, 'Pacific Heights': 11, 'Mission District': 26, 'Alamo Square': 19, 'Golden Gate Park': 12},
    'Marina District': {'Presidio': 10, 'The Castro': 22, 'Fisherman\'s Wharf': 10, 'Bayview': 27, 'Pacific Heights': 7, 'Mission District': 20, 'Alamo Square': 15, 'Golden Gate Park': 18},
    'The Castro': {'Presidio': 20, 'Marina District': 21, 'Fisherman\'s Wharf': 24, 'Bayview': 19, 'Pacific Heights': 16, 'Mission District': 7, 'Alamo Square': 8, 'Golden Gate Park': 11},
    'Fisherman\'s Wharf': {'Presidio': 17, 'Marina District': 9, 'The Castro': 27, 'Bayview': 26, 'Pacific Heights': 12, 'Mission District': 22, 'Alamo Square': 21, 'Golden Gate Park': 25},
    'Bayview': {'Presidio': 32, 'Marina District': 27, 'The Castro': 19, 'Fisherman\'s Wharf': 25, 'Pacific Heights': 23, 'Mission District': 13, 'Alamo Square': 16, 'Golden Gate Park': 22},
    'Pacific Heights': {'Presidio': 11, 'Marina District': 6, 'The Castro': 16, 'Fisherman\'s Wharf': 13, 'Bayview': 22, 'Mission District': 15, 'Alamo Square': 10, 'Golden Gate Park': 15},
    'Mission District': {'Presidio': 25, 'Marina District': 19, 'The Castro': 7, 'Fisherman\'s Wharf': 22, 'Bayview': 14, 'Pacific Heights': 16, 'Alamo Square': 11, 'Golden Gate Park': 17},
    'Alamo Square': {'Presidio': 17, 'Marina District': 15, 'The Castro': 8, 'Fisherman\'s Wharf': 19, 'Bayview': 16, 'Pacific Heights': 10, 'Mission District': 10, 'Golden Gate Park': 9},
    'Golden Gate Park': {'Presidio': 11, 'Marina District': 16, 'The Castro': 13, 'Fisherman\'s Wharf': 24, 'Bayview': 23, 'Pacific Heights': 16, 'Mission District': 17, 'Alamo Square': 9}
}

heap = []
heapq.heappush(heap, (0, 540, 'Presidio', 0, []))
best_times = {}
max_friends = 0
best_itinerary = []

while heap:
    priority, current_time, current_loc, met_mask, itinerary = heapq.heappop(heap)
    num_met = -priority

    if num_met > max_friends:
        max_friends = num_met
        best_itinerary = itinerary

    if num_met == len(friends):
        break

    key = (current_loc, met_mask)
    if key in best_times and best_times[key] <= current_time:
        continue
    best_times[key] = current_time

    for idx, friend in enumerate(friends):
        if not (met_mask & (1 << idx)):
            to_loc = friend['location']
            travel_duration = travel_time[current_loc].get(to_loc, float('inf'))
            if travel_duration == float('inf'):
                continue

            arrival_time = current_time + travel_duration
            start_time = max(arrival_time, friend['start'])
            end_time = start_time + friend['duration']

            if end_time > friend['end']:
                continue

            new_met_mask = met_mask | (1 << idx)
            new_priority = -(num_met + 1)
            new_itinerary = itinerary + [{
                'action': 'meet',
                'location': to_loc,
                'person': friend['name'],
                'start_time': minutes_to_time(start_time),
                'end_time': minutes_to_time(end_time)
            }]

            new_key = (to_loc, new_met_mask)
            if new_key not in best_times or end_time < best_times.get(new_key, float('inf')):
                heapq.heappush(heap, (new_priority, end_time, to_loc, new_met_mask, new_itinerary))

print(json.dumps({'itinerary': best_itinerary}))