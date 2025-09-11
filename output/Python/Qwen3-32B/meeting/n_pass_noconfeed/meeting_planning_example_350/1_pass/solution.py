import itertools
import json

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def parse_end_time(end_str):
    h, m = map(int, end_str.split(':'))
    return h * 60 + m

# Define friends
friends = [
    {
        'name': 'Mary',
        'location': 'Pacific Heights',
        'start_time': 10 * 60,  # 10:00 AM
        'end_time': 19 * 60,    # 7:00 PM
        'duration': 45
    },
    {
        'name': 'Lisa',
        'location': 'Mission District',
        'start_time': 20 * 60 + 30,  # 8:30 PM
        'end_time': 22 * 60,         # 10:00 PM
        'duration': 75
    },
    {
        'name': 'Betty',
        'location': 'Haight-Ashbury',
        'start_time': 7 * 60 + 15,   # 7:15 AM
        'end_time': 17 * 60 + 15,    # 5:15 PM
        'duration': 90
    },
    {
        'name': 'Charles',
        'location': 'Financial District',
        'start_time': 11 * 60 + 15,  # 11:15 AM
        'end_time': 15 * 60,         # 3:00 PM
        'duration': 120
    }
]

# Define travel times between locations
travel_time = {
    'Bayview': {
        'Pacific Heights': 23,
        'Mission District': 13,
        'Haight-Ashbury': 19,
        'Financial District': 19,
    },
    'Pacific Heights': {
        'Bayview': 22,
        'Mission District': 15,
        'Haight-Ashbury': 11,
        'Financial District': 13,
    },
    'Mission District': {
        'Bayview': 15,
        'Pacific Heights': 16,
        'Haight-Ashbury': 12,
        'Financial District': 17,
    },
    'Haight-Ashbury': {
        'Bayview': 18,
        'Pacific Heights': 12,
        'Mission District': 11,
        'Financial District': 21,
    },
    'Financial District': {
        'Bayview': 19,
        'Pacific Heights': 13,
        'Mission District': 17,
        'Haight-Ashbury': 19,
    },
}

def check_permutation(perm):
    current_time = 9 * 60  # 9:00 AM in minutes
    current_location = 'Bayview'
    itinerary = []
    for friend in perm:
        dest = friend['location']
        # Calculate travel time
        travel_duration = travel_time[current_location][dest]
        arrival_time = current_time + travel_duration

        # Check if can meet friend
        friend_start = friend['start_time']
        friend_end = friend['end_time']
        required = friend['duration']

        earliest_start = max(arrival_time, friend_start)
        meeting_end = earliest_start + required

        if meeting_end > friend_end:
            return None  # Invalid

        # Add to itinerary
        itinerary.append({
            'action': 'meet',
            'location': dest,
            'person': friend['name'],
            'start_time': minutes_to_time(earliest_start),
            'end_time': minutes_to_time(meeting_end)
        })

        # Update current time and location
        current_time = meeting_end
        current_location = dest

    return itinerary

best_itinerary = None
best_length = 0
best_end_time = float('inf')

for r in range(1, len(friends)+1):
    for perm in itertools.permutations(friends, r):
        result = check_permutation(perm)
        if result is not None:
            current_len = len(result)
            if current_len > best_length:
                best_length = current_len
                best_itinerary = result
                best_end_time = parse_end_time(result[-1]['end_time'])
            elif current_len == best_length:
                current_result_end = parse_end_time(result[-1]['end_time'])
                if current_result_end < best_end_time:
                    best_itinerary = result
                    best_end_time = current_result_end

# Output the result
output = {
    "itinerary": best_itinerary
}

print(json.dumps(output, indent=2))