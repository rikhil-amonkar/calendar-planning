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
    # Travel times in minutes (from: {to: time})
    travel_times = {
        'The Castro': {
            'Bayview': 19,
            'Pacific Heights': 16,
            'Alamo Square': 8,
            'Fisherman\'s Wharf': 24,
            'Golden Gate Park': 11
        },
        'Bayview': {
            'The Castro': 20,
            'Pacific Heights': 23,
            'Alamo Square': 16,
            'Fisherman\'s Wharf': 25,
            'Golden Gate Park': 22
        },
        'Pacific Heights': {
            'The Castro': 16,
            'Bayview': 22,
            'Alamo Square': 10,
            'Fisherman\'s Wharf': 13,
            'Golden Gate Park': 15
        },
        'Alamo Square': {
            'The Castro': 8,
            'Bayview': 16,
            'Pacific Heights': 10,
            'Fisherman\'s Wharf': 19,
            'Golden Gate Park': 9
        },
        'Fisherman\'s Wharf': {
            'The Castro': 26,
            'Bayview': 26,
            'Pacific Heights': 12,
            'Alamo Square': 20,
            'Golden Gate Park': 25
        },
        'Golden Gate Park': {
            'The Castro': 13,
            'Bayview': 23,
            'Pacific Heights': 16,
            'Alamo Square': 10,
            'Fisherman\'s Wharf': 24
        }
    }

    # Friend constraints
    friends = {
        'Rebecca': {
            'location': 'Bayview',
            'available_start': '9:00',
            'available_end': '12:45',
            'min_duration': 90
        },
        'Amanda': {
            'location': 'Pacific Heights',
            'available_start': '18:30',
            'available_end': '21:45',
            'min_duration': 90
        },
        'James': {
            'location': 'Alamo Square',
            'available_start': '9:45',
            'available_end': '21:15',
            'min_duration': 90
        },
        'Sarah': {
            'location': 'Fisherman\'s Wharf',
            'available_start': '8:00',
            'available_end': '21:30',
            'min_duration': 90
        },
        'Melissa': {
            'location': 'Golden Gate Park',
            'available_start': '9:00',
            'available_end': '18:45',
            'min_duration': 90
        }
    }

    current_location = 'The Castro'
    current_time = time_to_minutes('9:00')
    itinerary = []

    # Try different permutations of friends to find the best schedule
    best_itinerary = None
    max_meetings = 0

    for friend_order in permutations(['Rebecca', 'Amanda', 'James', 'Sarah', 'Melissa']):
        temp_itinerary = []
        temp_location = current_location
        temp_time = current_time
        meetings = 0

        for friend in friend_order:
            data = friends[friend]
            location = data['location']
            available_start = time_to_minutes(data['available_start'])
            available_end = time_to_minutes(data['available_end'])
            min_duration = data['min_duration']

            # Calculate travel time
            travel_time = travel_times[temp_location][location]
            arrival_time = temp_time + travel_time

            # Check if we can meet within the available window
            start_time = max(arrival_time, available_start)
            end_time = start_time + min_duration

            if end_time <= available_end:
                temp_itinerary.append({
                    'action': 'meet',
                    'location': location,
                    'person': friend,
                    'start_time': minutes_to_time(start_time),
                    'end_time': minutes_to_time(end_time)
                })
                meetings += 1
                temp_location = location
                temp_time = end_time

        if meetings > max_meetings:
            max_meetings = meetings
            best_itinerary = temp_itinerary

    return {'itinerary': best_itinerary}

if __name__ == "__main__":
    schedule = calculate_schedule()
    print(json.dumps(schedule, indent=2))