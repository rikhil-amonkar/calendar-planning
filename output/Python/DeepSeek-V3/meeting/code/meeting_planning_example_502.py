import json
from itertools import permutations

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def calculate_schedule():
    # Travel times dictionary: {from_location: {to_location: minutes}}
    travel_times = {
        'Financial District': {
            'Golden Gate Park': 23,
            'Chinatown': 5,
            'Union Square': 9,
            'Fisherman\'s Wharf': 10,
            'Pacific Heights': 13,
            'North Beach': 7
        },
        'Golden Gate Park': {
            'Financial District': 26,
            'Chinatown': 23,
            'Union Square': 22,
            'Fisherman\'s Wharf': 24,
            'Pacific Heights': 16,
            'North Beach': 24
        },
        'Chinatown': {
            'Financial District': 5,
            'Golden Gate Park': 23,
            'Union Square': 7,
            'Fisherman\'s Wharf': 8,
            'Pacific Heights': 10,
            'North Beach': 3
        },
        'Union Square': {
            'Financial District': 9,
            'Golden Gate Park': 22,
            'Chinatown': 7,
            'Fisherman\'s Wharf': 15,
            'Pacific Heights': 15,
            'North Beach': 10
        },
        'Fisherman\'s Wharf': {
            'Financial District': 11,
            'Golden Gate Park': 25,
            'Chinatown': 12,
            'Union Square': 13,
            'Pacific Heights': 12,
            'North Beach': 6
        },
        'Pacific Heights': {
            'Financial District': 13,
            'Golden Gate Park': 15,
            'Chinatown': 11,
            'Union Square': 12,
            'Fisherman\'s Wharf': 13,
            'North Beach': 9
        },
        'North Beach': {
            'Financial District': 8,
            'Golden Gate Park': 22,
            'Chinatown': 6,
            'Union Square': 7,
            'Fisherman\'s Wharf': 5,
            'Pacific Heights': 8
        }
    }

    # Friend constraints
    friends = [
        {'name': 'Stephanie', 'location': 'Golden Gate Park', 'start': '11:00', 'end': '15:00', 'duration': 105},
        {'name': 'Karen', 'location': 'Chinatown', 'start': '13:45', 'end': '16:30', 'duration': 15},
        {'name': 'Brian', 'location': 'Union Square', 'start': '15:00', 'end': '17:15', 'duration': 30},
        {'name': 'Rebecca', 'location': 'Fisherman\'s Wharf', 'start': '8:00', 'end': '11:15', 'duration': 30},
        {'name': 'Joseph', 'location': 'Pacific Heights', 'start': '8:15', 'end': '9:30', 'duration': 60},
        {'name': 'Steven', 'location': 'North Beach', 'start': '14:30', 'end': '20:45', 'duration': 120}
    ]

    current_time = time_to_minutes('9:00')
    current_location = 'Financial District'
    itinerary = []

    # Try to meet Joseph first (earliest availability)
    joseph = next(f for f in friends if f['name'] == 'Joseph')
    travel_time = travel_times[current_location][joseph['location']]
    arrival_time = current_time + travel_time
    joseph_start = time_to_minutes(joseph['start'])
    joseph_end = time_to_minutes(joseph['end'])
    
    if arrival_time <= joseph_end - joseph['duration']:
        meet_start = max(arrival_time, joseph_start)
        meet_end = meet_start + joseph['duration']
        if meet_end <= joseph_end:
            itinerary.append({
                'action': 'meet',
                'location': joseph['location'],
                'person': joseph['name'],
                'start_time': minutes_to_time(meet_start),
                'end_time': minutes_to_time(meet_end)
            })
            current_time = meet_end
            current_location = joseph['location']

    # Try to meet Rebecca next
    rebecca = next(f for f in friends if f['name'] == 'Rebecca')
    travel_time = travel_times[current_location][rebecca['location']]
    arrival_time = current_time + travel_time
    rebecca_start = time_to_minutes(rebecca['start'])
    rebecca_end = time_to_minutes(rebecca['end'])
    
    if arrival_time <= rebecca_end - rebecca['duration']:
        meet_start = max(arrival_time, rebecca_start)
        meet_end = meet_start + rebecca['duration']
        if meet_end <= rebecca_end:
            itinerary.append({
                'action': 'meet',
                'location': rebecca['location'],
                'person': rebecca['name'],
                'start_time': minutes_to_time(meet_start),
                'end_time': minutes_to_time(meet_end)
            })
            current_time = meet_end
            current_location = rebecca['location']

    # Try to meet Stephanie next
    stephanie = next(f for f in friends if f['name'] == 'Stephanie')
    travel_time = travel_times[current_location][stephanie['location']]
    arrival_time = current_time + travel_time
    stephanie_start = time_to_minutes(stephanie['start'])
    stephanie_end = time_to_minutes(stephanie['end'])
    
    if arrival_time <= stephanie_end - stephanie['duration']:
        meet_start = max(arrival_time, stephanie_start)
        meet_end = meet_start + stephanie['duration']
        if meet_end <= stephanie_end:
            itinerary.append({
                'action': 'meet',
                'location': stephanie['location'],
                'person': stephanie['name'],
                'start_time': minutes_to_time(meet_start),
                'end_time': minutes_to_time(meet_end)
            })
            current_time = meet_end
            current_location = stephanie['location']

    # Try to meet Karen next
    karen = next(f for f in friends if f['name'] == 'Karen')
    travel_time = travel_times[current_location][karen['location']]
    arrival_time = current_time + travel_time
    karen_start = time_to_minutes(karen['start'])
    karen_end = time_to_minutes(karen['end'])
    
    if arrival_time <= karen_end - karen['duration']:
        meet_start = max(arrival_time, karen_start)
        meet_end = meet_start + karen['duration']
        if meet_end <= karen_end:
            itinerary.append({
                'action': 'meet',
                'location': karen['location'],
                'person': karen['name'],
                'start_time': minutes_to_time(meet_start),
                'end_time': minutes_to_time(meet_end)
            })
            current_time = meet_end
            current_location = karen['location']

    # Try to meet Steven next
    steven = next(f for f in friends if f['name'] == 'Steven')
    travel_time = travel_times[current_location][steven['location']]
    arrival_time = current_time + travel_time
    steven_start = time_to_minutes(steven['start'])
    steven_end = time_to_minutes(steven['end'])
    
    if arrival_time <= steven_end - steven['duration']:
        meet_start = max(arrival_time, steven_start)
        meet_end = meet_start + steven['duration']
        if meet_end <= steven_end:
            itinerary.append({
                'action': 'meet',
                'location': steven['location'],
                'person': steven['name'],
                'start_time': minutes_to_time(meet_start),
                'end_time': minutes_to_time(meet_end)
            })
            current_time = meet_end
            current_location = steven['location']

    # Try to meet Brian last
    brian = next(f for f in friends if f['name'] == 'Brian')
    travel_time = travel_times[current_location][brian['location']]
    arrival_time = current_time + travel_time
    brian_start = time_to_minutes(brian['start'])
    brian_end = time_to_minutes(brian['end'])
    
    if arrival_time <= brian_end - brian['duration']:
        meet_start = max(arrival_time, brian_start)
        meet_end = meet_start + brian['duration']
        if meet_end <= brian_end:
            itinerary.append({
                'action': 'meet',
                'location': brian['location'],
                'person': brian['name'],
                'start_time': minutes_to_time(meet_start),
                'end_time': minutes_to_time(meet_end)
            })

    return {'itinerary': itinerary}

if __name__ == '__main__':
    schedule = calculate_schedule()
    print(json.dumps(schedule, indent=2))