import itertools
import json

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

travel_times = {
    'Castro': {'Alamo Square': 8, 'Union Square': 19, 'Chinatown': 20},
    'Alamo Square': {'Castro': 8, 'Union Square': 14, 'Chinatown': 16},
    'Union Square': {'Castro': 19, 'Alamo Square': 15, 'Chinatown': 7},
    'Chinatown': {'Castro': 22, 'Alamo Square': 17, 'Union Square': 7},
}

friends = [
    {
        'name': 'Emily',
        'location': 'Alamo Square',
        'available_start': '11:45',
        'available_end': '15:15',
        'required_duration': 105
    },
    {
        'name': 'Barbara',
        'location': 'Union Square',
        'available_start': '16:45',
        'available_end': '18:15',
        'required_duration': 60
    },
    {
        'name': 'William',
        'location': 'Chinatown',
        'available_start': '17:15',
        'available_end': '19:00',
        'required_duration': 105
    }
]

best_itinerary = []
max_met = 0

# Initial state
start_location = 'Castro'
start_time = time_to_minutes('9:00')

for r in range(1, len(friends)+1):
    for perm in itertools.permutations(friends, r):
        current_time = start_time
        current_location = start_location
        itinerary = []
        met_count = 0

        for friend in perm:
            # Calculate travel time
            travel_time = travel_times[current_location][friend['location']]
            arrival_time = current_time + travel_time

            # Check if arrival is before available end
            available_end = time_to_minutes(friend['available_end'])
            if arrival_time > available_end:
                break  # can't meet this friend

            # Determine start meeting time
            available_start = time_to_minutes(friend['available_start'])
            start_meeting = max(arrival_time, available_start)

            # Check if meeting can fit
            end_meeting = start_meeting + friend['required_duration']
            if end_meeting > available_end:
                break  # can't meet

            # Add to itinerary
            itinerary.append({
                'action': 'meet',
                'location': friend['location'],
                'person': friend['name'],
                'start_time': minutes_to_time(start_meeting),
                'end_time': minutes_to_time(end_meeting)
            })
            met_count += 1

            # Update current time and location
            current_time = end_meeting
            current_location = friend['location']

        # Check if this is the best so far
        if met_count > max_met:
            max_met = met_count
            best_itinerary = itinerary

# Output the result as JSON
result = {"itinerary": best_itinerary}
print(json.dumps(result, indent=2))