import json

def time_to_minutes(time_str):
    hours, mins = map(int, time_str.split(':'))
    return hours * 60 + mins

def minutes_to_time(mins):
    hours = mins // 60
    mins = mins % 60
    return f"{hours}:{mins:02d}"

travel_times = {
    ('Richmond District', 'Pacific Heights'): 10,
    ('Richmond District', 'Marina District'): 9,
    ('Pacific Heights', 'Richmond District'): 12,
    ('Pacific Heights', 'Marina District'): 6,
    ('Marina District', 'Richmond District'): 11,
    ('Marina District', 'Pacific Heights'): 7
}

friends = [
    {
        'name': 'Jessica',
        'location': 'Pacific Heights',
        'available_start': '15:30',
        'available_end': '16:45',
        'required_duration': 45
    },
    {
        'name': 'Carol',
        'location': 'Marina District',
        'available_start': '11:30',
        'available_end': '15:00',
        'required_duration': 60
    }
]

current_time = 540  # 9:00 AM in minutes
current_location = 'Richmond District'

best_itinerary = []

# Try both possible orders
for order in [('Jessica', 'Carol'), ('Carol', 'Jessica')]:
    itinerary = []
    temp_time = current_time
    temp_loc = current_location
    valid = True

    for friend_name in order:
        friend = next(f for f in friends if f['name'] == friend_name)
        travel = travel_times.get((temp_loc, friend['location']), None)
        if travel is None:
            valid = False
            break
        arrival_time = temp_time + travel

        avail_start = time_to_minutes(friend['available_start'])
        avail_end = time_to_minutes(friend['available_end'])

        start_time = max(arrival_time, avail_start)
        end_time = start_time + friend['required_duration']

        if end_time > avail_end:
            valid = False
            break

        itinerary.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': minutes_to_time(start_time),
            'end_time': minutes_to_time(end_time)
        })

        temp_time = end_time
        temp_loc = friend['location']

    if valid and len(itinerary) > len(best_itinerary):
        best_itinerary = itinerary

result = {'itinerary': best_itinerary}
print(json.dumps(result))