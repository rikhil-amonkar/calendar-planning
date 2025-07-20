import json
from itertools import permutations

def time_to_minutes(time_str):
    parts = time_str.split(':')
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02}"

travel_times = {
    'Sunset District': {'Chinatown': 30, 'Russian Hill': 24, 'North Beach': 29},
    'Chinatown': {'Sunset District': 29, 'Russian Hill': 7, 'North Beach': 3},
    'Russian Hill': {'Sunset District': 23, 'Chinatown': 9, 'North Beach': 5},
    'North Beach': {'Sunset District': 27, 'Chinatown': 6, 'Russian Hill': 4}
}

friends_data = [
    {'name': 'Melissa', 'location': 'North Beach', 'start_avail': '8:15', 'end_avail': '13:30', 'min_duration': 105},
    {'name': 'Anthony', 'location': 'Chinatown', 'start_avail': '13:15', 'end_avail': '14:30', 'min_duration': 60},
    {'name': 'Rebecca', 'location': 'Russian Hill', 'start_avail': '19:30', 'end_avail': '21:15', 'min_duration': 105}
]

for friend in friends_data:
    friend['start_avail'] = time_to_minutes(friend['start_avail'])
    friend['end_avail'] = time_to_minutes(friend['end_avail'])

start_location = 'Sunset District'
start_time = time_to_minutes('9:00')
best_itinerary = None
best_count = 0

for order in permutations(range(3)):
    current_location = start_location
    current_time = start_time
    itinerary_temp = []
    for i, idx in enumerate(order):
        friend = friends_data[idx]
        travel_time = travel_times[current_location][friend['location']]
        current_time += travel_time
        meeting_start = max(current_time, friend['start_avail'])
        if i < len(order) - 1:
            next_friend = friends_data[order[i+1]]
            travel_to_next = travel_times[friend['location']][next_friend['location']]
            leave_by = next_friend['start_avail'] - travel_to_next
        else:
            leave_by = friend['end_avail']
        meeting_end = min(friend['end_avail'], leave_by)
        if meeting_end - meeting_start >= friend['min_duration']:
            itinerary_temp.append({
                'action': 'meet',
                'location': friend['location'],
                'person': friend['name'],
                'start_time': minutes_to_time(meeting_start),
                'end_time': minutes_to_time(meeting_end)
            })
            current_time = meeting_end
            current_location = friend['location']
        else:
            current_location = friend['location']
    count = len(itinerary_temp)
    if count == 3:
        best_itinerary = itinerary_temp
        break
    elif count > best_count:
        best_count = count
        best_itinerary = itinerary_temp

result = {"itinerary": best_itinerary}
print(json.dumps(result))