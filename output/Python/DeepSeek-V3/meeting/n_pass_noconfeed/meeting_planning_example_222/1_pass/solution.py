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
    # Travel times in minutes
    travel_times = {
        ('Nob Hill', 'North Beach'): 8,
        ('Nob Hill', 'Fisherman\'s Wharf'): 11,
        ('Nob Hill', 'Bayview'): 19,
        ('North Beach', 'Nob Hill'): 7,
        ('North Beach', 'Fisherman\'s Wharf'): 5,
        ('North Beach', 'Bayview'): 22,
        ('Fisherman\'s Wharf', 'Nob Hill'): 11,
        ('Fisherman\'s Wharf', 'North Beach'): 6,
        ('Fisherman\'s Wharf', 'Bayview'): 26,
        ('Bayview', 'Nob Hill'): 20,
        ('Bayview', 'North Beach'): 21,
        ('Bayview', 'Fisherman\'s Wharf'): 25
    }

    # Constraints
    current_location = 'Nob Hill'
    current_time = time_to_minutes('9:00')

    friends = [
        {
            'name': 'Helen',
            'location': 'North Beach',
            'available_start': time_to_minutes('7:00'),
            'available_end': time_to_minutes('16:45'),
            'min_duration': 120
        },
        {
            'name': 'Kimberly',
            'location': 'Fisherman\'s Wharf',
            'available_start': time_to_minutes('16:30'),
            'available_end': time_to_minutes('21:00'),
            'min_duration': 45
        },
        {
            'name': 'Patricia',
            'location': 'Bayview',
            'available_start': time_to_minutes('18:00'),
            'available_end': time_to_minutes('21:15'),
            'min_duration': 120
        }
    ]

    best_itinerary = []
    max_meetings = 0

    # Try all possible orders of meeting friends
    for order in permutations(friends):
        itinerary = []
        temp_location = current_location
        temp_time = current_time
        possible = True
        meetings = 0

        for friend in order:
            # Calculate travel time
            travel_time = travel_times[(temp_location, friend['location'])]
            arrival_time = temp_time + travel_time

            # Check if we can meet the friend
            start_time = max(arrival_time, friend['available_start'])
            end_time = start_time + friend['min_duration']

            if end_time > friend['available_end']:
                possible = False
                break

            itinerary.append({
                'action': 'meet',
                'location': friend['location'],
                'person': friend['name'],
                'start_time': minutes_to_time(start_time),
                'end_time': minutes_to_time(end_time)
            })

            temp_location = friend['location']
            temp_time = end_time
            meetings += 1

        if possible and meetings > max_meetings:
            max_meetings = meetings
            best_itinerary = itinerary

    # If no order allows meeting all, try subsets
    if max_meetings < 3:
        for friend in friends:
            temp_location = current_location
            temp_time = current_time
            itinerary = []
            meetings = 0

            travel_time = travel_times[(temp_location, friend['location'])]
            arrival_time = temp_time + travel_time

            start_time = max(arrival_time, friend['available_start'])
            end_time = start_time + friend['min_duration']

            if end_time <= friend['available_end']:
                itinerary.append({
                    'action': 'meet',
                    'location': friend['location'],
                    'person': friend['name'],
                    'start_time': minutes_to_time(start_time),
                    'end_time': minutes_to_time(end_time)
                })
                meetings = 1

            if meetings > max_meetings:
                max_meetings = meetings
                best_itinerary = itinerary

        # Try pairs
        for i in range(len(friends)):
            for j in range(i+1, len(friends)):
                temp_location = current_location
                temp_time = current_time
                itinerary = []
                possible = True
                meetings = 0

                # First friend
                friend1 = friends[i]
                travel_time = travel_times[(temp_location, friend1['location'])]
                arrival_time = temp_time + travel_time
                start_time = max(arrival_time, friend1['available_start'])
                end_time = start_time + friend1['min_duration']

                if end_time > friend1['available_end']:
                    possible = False
                else:
                    itinerary.append({
                        'action': 'meet',
                        'location': friend1['location'],
                        'person': friend1['name'],
                        'start_time': minutes_to_time(start_time),
                        'end_time': minutes_to_time(end_time)
                    })
                    temp_location = friend1['location']
                    temp_time = end_time
                    meetings += 1

                    # Second friend
                    friend2 = friends[j]
                    travel_time = travel_times[(temp_location, friend2['location'])]
                    arrival_time = temp_time + travel_time
                    start_time = max(arrival_time, friend2['available_start'])
                    end_time = start_time + friend2['min_duration']

                    if end_time > friend2['available_end']:
                        possible = False
                    else:
                        itinerary.append({
                            'action': 'meet',
                            'location': friend2['location'],
                            'person': friend2['name'],
                            'start_time': minutes_to_time(start_time),
                            'end_time': minutes_to_time(end_time)
                        })
                        meetings += 1

                if possible and meetings > max_meetings:
                    max_meetings = meetings
                    best_itinerary = itinerary

    return {'itinerary': best_itinerary}

result = calculate_schedule()
print(json.dumps(result, indent=2))