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
    # Travel times dictionary: {from: {to: minutes}}
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
        {
            'name': 'Stephanie',
            'location': 'Golden Gate Park',
            'start': time_to_minutes('11:00'),
            'end': time_to_minutes('15:00'),
            'duration': 105
        },
        {
            'name': 'Karen',
            'location': 'Chinatown',
            'start': time_to_minutes('13:45'),
            'end': time_to_minutes('16:30'),
            'duration': 15
        },
        {
            'name': 'Brian',
            'location': 'Union Square',
            'start': time_to_minutes('15:00'),
            'end': time_to_minutes('17:15'),
            'duration': 30
        },
        {
            'name': 'Rebecca',
            'location': 'Fisherman\'s Wharf',
            'start': time_to_minutes('8:00'),
            'end': time_to_minutes('11:15'),
            'duration': 30
        },
        {
            'name': 'Joseph',
            'location': 'Pacific Heights',
            'start': time_to_minutes('8:15'),
            'end': time_to_minutes('9:30'),
            'duration': 60
        },
        {
            'name': 'Steven',
            'location': 'North Beach',
            'start': time_to_minutes('14:30'),
            'end': time_to_minutes('20:45'),
            'duration': 120
        }
    ]

    # Filter friends that can be met based on arrival time (9:00 at Financial District)
    feasible_friends = [f for f in friends if f['name'] not in ['Rebecca', 'Joseph']]
    # Joseph is only available before 9:30, and we arrive at 9:00 - can we meet him?
    current_time = time_to_minutes('9:00')
    joseph = next(f for f in friends if f['name'] == 'Joseph')
    travel_to_joseph = travel_times['Financial District'][joseph['location']]
    if current_time + travel_to_joseph <= joseph['end'] - joseph['duration']:
        feasible_friends.append(joseph)

    # Generate all possible orders to meet friends
    best_schedule = None
    max_meetings = 0

    for order in permutations(feasible_friends):
        schedule = []
        current_location = 'Financial District'
        current_time = time_to_minutes('9:00')
        meetings = 0

        # Try to meet Joseph first if in the order
        temp_order = list(order)
        if joseph in temp_order:
            idx = temp_order.index(joseph)
            if idx != 0:
                temp_order.pop(idx)
                temp_order.insert(0, joseph)

        for friend in temp_order:
            # Calculate travel time
            travel_time = travel_times[current_location][friend['location']]
            arrival_time = current_time + travel_time

            # Check if we can meet the friend
            meeting_start = max(arrival_time, friend['start'])
            meeting_end = meeting_start + friend['duration']

            if meeting_end <= friend['end']:
                schedule.append({
                    'action': 'meet',
                    'location': friend['location'],
                    'person': friend['name'],
                    'start_time': minutes_to_time(meeting_start),
                    'end_time': minutes_to_time(meeting_end)
                })
                meetings += 1
                current_time = meeting_end
                current_location = friend['location']
            else:
                break

        if meetings > max_meetings or (meetings == max_meetings and len(schedule) > len(best_schedule)):
            max_meetings = meetings
            best_schedule = schedule

    # After trying all orders, check if we can meet Rebecca (she's available before 11:15)
    # Try to insert Rebecca at the beginning if possible
    rebecca = next(f for f in friends if f['name'] == 'Rebecca')
    travel_to_rebecca = travel_times['Financial District'][rebecca['location']]
    meeting_start = max(time_to_minutes('9:00') + travel_to_rebecca, rebecca['start'])
    meeting_end = meeting_start + rebecca['duration']
    if meeting_end <= rebecca['end']:
        # Check if this affects other meetings
        temp_schedule = [{
            'action': 'meet',
            'location': rebecca['location'],
            'person': rebecca['name'],
            'start_time': minutes_to_time(meeting_start),
            'end_time': minutes_to_time(meeting_end)
        }]
        current_time_after_rebecca = meeting_end
        current_location_after_rebecca = rebecca['location']
        additional_meetings = 0

        # Try to meet other friends after Rebecca
        remaining_friends = [f for f in feasible_friends if f['name'] != rebecca['name']]
        for friend in remaining_friends:
            travel_time = travel_times[current_location_after_rebecca][friend['location']]
            arrival_time = current_time_after_rebecca + travel_time
            meeting_start = max(arrival_time, friend['start'])
            meeting_end = meeting_start + friend['duration']
            if meeting_end <= friend['end']:
                temp_schedule.append({
                    'action': 'meet',
                    'location': friend['location'],
                    'person': friend['name'],
                    'start_time': minutes_to_time(meeting_start),
                    'end_time': minutes_to_time(meeting_end)
                })
                additional_meetings += 1
                current_time_after_rebecca = meeting_end
                current_location_after_rebecca = friend['location']
            else:
                break

        if (1 + additional_meetings) > max_meetings:
            max_meetings = 1 + additional_meetings
            best_schedule = temp_schedule

    return {'itinerary': best_schedule}

if __name__ == '__main__':
    schedule = calculate_schedule()
    print(json.dumps(schedule, indent=2))