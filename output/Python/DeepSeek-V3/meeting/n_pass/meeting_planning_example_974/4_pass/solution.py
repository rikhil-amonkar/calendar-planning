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
        'Sunset District': {
            'Presidio': 16, 'Nob Hill': 27, 'Pacific Heights': 21, 'Mission District': 25,
            'Marina District': 21, 'North Beach': 28, 'Russian Hill': 24, 'Richmond District': 12,
            'Embarcadero': 30, 'Alamo Square': 17
        },
        'Presidio': {
            'Sunset District': 15, 'Nob Hill': 18, 'Pacific Heights': 11, 'Mission District': 26,
            'Marina District': 11, 'North Beach': 18, 'Russian Hill': 14, 'Richmond District': 7,
            'Embarcadero': 20, 'Alamo Square': 19
        },
        'Nob Hill': {
            'Sunset District': 24, 'Presidio': 17, 'Pacific Heights': 8, 'Mission District': 13,
            'Marina District': 11, 'North Beach': 8, 'Russian Hill': 5, 'Richmond District': 14,
            'Embarcadero': 9, 'Alamo Square': 11
        },
        'Pacific Heights': {
            'Sunset District': 21, 'Presidio': 11, 'Nob Hill': 8, 'Mission District': 15,
            'Marina District': 6, 'North Beach': 9, 'Russian Hill': 7, 'Richmond District': 12,
            'Embarcadero': 10, 'Alamo Square': 10
        },
        'Mission District': {
            'Sunset District': 24, 'Presidio': 25, 'Nob Hill': 12, 'Pacific Heights': 16,
            'Marina District': 19, 'North Beach': 17, 'Russian Hill': 15, 'Richmond District': 20,
            'Embarcadero': 19, 'Alamo Square': 11
        },
        'Marina District': {
            'Sunset District': 19, 'Presidio': 10, 'Nob Hill': 12, 'Pacific Heights': 7,
            'Mission District': 20, 'North Beach': 11, 'Russian Hill': 8, 'Richmond District': 11,
            'Embarcadero': 14, 'Alamo Square': 15
        },
        'North Beach': {
            'Sunset District': 27, 'Presidio': 17, 'Nob Hill': 7, 'Pacific Heights': 8,
            'Mission District': 18, 'Marina District': 9, 'Russian Hill': 4, 'Richmond District': 18,
            'Embarcadero': 6, 'Alamo Square': 16
        },
        'Russian Hill': {
            'Sunset District': 23, 'Presidio': 14, 'Nob Hill': 5, 'Pacific Heights': 7,
            'Mission District': 16, 'Marina District': 7, 'North Beach': 5, 'Richmond District': 14,
            'Embarcadero': 8, 'Alamo Square': 15
        },
        'Richmond District': {
            'Sunset District': 11, 'Presidio': 7, 'Nob Hill': 17, 'Pacific Heights': 10,
            'Mission District': 20, 'Marina District': 9, 'North Beach': 17, 'Russian Hill': 13,
            'Embarcadero': 19, 'Alamo Square': 13
        },
        'Embarcadero': {
            'Sunset District': 30, 'Presidio': 20, 'Nob Hill': 10, 'Pacific Heights': 11,
            'Mission District': 20, 'Marina District': 12, 'North Beach': 5, 'Russian Hill': 8,
            'Richmond District': 21, 'Alamo Square': 19
        },
        'Alamo Square': {
            'Sunset District': 16, 'Presidio': 17, 'Nob Hill': 11, 'Pacific Heights': 10,
            'Mission District': 10, 'Marina District': 15, 'North Beach': 15, 'Russian Hill': 13,
            'Richmond District': 11, 'Embarcadero': 16
        }
    }

    # Friend constraints: {name: (location, start_min, end_min, duration_min)}
    friends = {
        'Charles': ('Presidio', time_to_minutes('13:15'), time_to_minutes('15:00'), 45),
        'Robert': ('Nob Hill', time_to_minutes('13:15'), time_to_minutes('17:30'), 90),
        'Nancy': ('Pacific Heights', time_to_minutes('14:45'), time_to_minutes('22:00'), 50),
        'Brian': ('Mission District', time_to_minutes('15:30'), time_to_minutes('22:00'), 60),
        'Kimberly': ('Marina District', time_to_minutes('17:00'), time_to_minutes('19:45'), 45),
        'David': ('North Beach', time_to_minutes('14:45'), time_to_minutes('16:30'), 45),
        'William': ('Russian Hill', time_to_minutes('12:30'), time_to_minutes('19:15'), 60),
        'Jeffrey': ('Richmond District', time_to_minutes('12:00'), time_to_minutes('19:15'), 45),
        'Karen': ('Embarcadero', time_to_minutes('14:15'), time_to_minutes('20:45'), 60),
        'Joshua': ('Alamo Square', time_to_minutes('18:45'), time_to_minutes('22:00'), 60)
    }

    # Start at Sunset District at 9:00
    current_time = time_to_minutes('9:00')
    current_location = 'Sunset District'
    best_itinerary = []
    max_meetings = 0

    # Try all permutations of friends to find the best schedule
    for perm in permutations(friends.keys()):
        temp_itinerary = []
        temp_current_time = current_time
        temp_current_location = current_location
        temp_met_friends = 0

        for friend in perm:
            location, start, end, duration = friends[friend]
            travel_time = travel_times[temp_current_location].get(location, float('inf'))
            
            # Calculate earliest possible meeting time
            arrival_time = temp_current_time + travel_time
            meeting_start = max(arrival_time, start)
            meeting_end = meeting_start + duration
            
            if meeting_end <= end:
                temp_itinerary.append({
                    'action': 'meet',
                    'location': location,
                    'person': friend,
                    'start_time': minutes_to_time(meeting_start),
                    'end_time': minutes_to_time(meeting_end)
                })
                temp_current_time = meeting_end
                temp_current_location = location
                temp_met_friends += 1
            else:
                # Try to fit a shorter meeting if possible
                possible_duration = end - meeting_start
                if possible_duration >= 30:  # Minimum meeting duration of 30 minutes
                    temp_itinerary.append({
                        'action': 'meet',
                        'location': location,
                        'person': friend,
                        'start_time': minutes_to_time(meeting_start),
                        'end_time': minutes_to_time(meeting_start + possible_duration)
                    })
                    temp_current_time = meeting_start + possible_duration
                    temp_current_location = location
                    temp_met_friends += 1

        if temp_met_friends > max_meetings or (temp_met_friends == max_meetings and len(temp_itinerary) > len(best_itinerary)):
            max_meetings = temp_met_friends
            best_itinerary = temp_itinerary

    return {'itinerary': best_itinerary}

if __name__ == '__main__':
    schedule = calculate_schedule()
    print(json.dumps(schedule, indent=2))