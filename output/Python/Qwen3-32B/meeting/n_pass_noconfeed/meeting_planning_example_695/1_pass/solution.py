import itertools
import json

def time_str_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time_str(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Define friends with their constraints
friends = [
    {
        'name': 'Paul',
        'location': 'Nob Hill',
        'available_start': time_str_to_minutes('16:15'),
        'available_end': time_str_to_minutes('21:15'),
        'required_duration': 60
    },
    {
        'name': 'Carol',
        'location': 'Union Square',
        'available_start': time_str_to_minutes('18:00'),
        'available_end': time_str_to_minutes('20:15'),
        'required_duration': 120
    },
    {
        'name': 'Patricia',
        'location': 'Chinatown',
        'available_start': time_str_to_minutes('20:00'),
        'available_end': time_str_to_minutes('21:30'),
        'required_duration': 75
    },
    {
        'name': 'Karen',
        'location': 'The Castro',
        'available_start': time_str_to_minutes('17:00'),
        'available_end': time_str_to_minutes('19:00'),
        'required_duration': 45
    },
    {
        'name': 'Nancy',
        'location': 'Presidio',
        'available_start': time_str_to_minutes('11:45'),
        'available_end': time_str_to_minutes('22:00'),
        'required_duration': 30
    },
    {
        'name': 'Jeffrey',
        'location': 'Pacific Heights',
        'available_start': time_str_to_minutes('20:00'),
        'available_end': time_str_to_minutes('20:45'),
        'required_duration': 45
    },
    {
        'name': 'Matthew',
        'location': 'Russian Hill',
        'available_start': time_str_to_minutes('15:45'),
        'available_end': time_str_to_minutes('21:45'),
        'required_duration': 75
    }
]

# Define travel times between locations
travel_times = {
    'Bayview': {
        'Nob Hill': 20,
        'Union Square': 17,
        'Chinatown': 18,
        'The Castro': 20,
        'Presidio': 31,
        'Pacific Heights': 23,
        'Russian Hill': 23
    },
    'Nob Hill': {
        'Bayview': 19,
        'Union Square': 7,
        'Chinatown': 6,
        'The Castro': 17,
        'Presidio': 17,
        'Pacific Heights': 8,
        'Russian Hill': 5
    },
    'Union Square': {
        'Bayview': 15,
        'Nob Hill': 9,
        'Chinatown': 7,
        'The Castro': 19,
        'Presidio': 24,
        'Pacific Heights': 15,
        'Russian Hill': 13
    },
    'Chinatown': {
        'Bayview': 22,
        'Nob Hill': 8,
        'Union Square': 7,
        'The Castro': 22,
        'Presidio': 19,
        'Pacific Heights': 10,
        'Russian Hill': 7
    },
    'The Castro': {
        'Bayview': 19,
        'Nob Hill': 16,
        'Union Square': 19,
        'Chinatown': 20,
        'Presidio': 20,
        'Pacific Heights': 16,
        'Russian Hill': 18
    },
    'Presidio': {
        'Bayview': 31,
        'Nob Hill': 18,
        'Union Square': 22,
        'Chinatown': 21,
        'The Castro': 21,
        'Pacific Heights': 11,
        'Russian Hill': 14
    },
    'Pacific Heights': {
        'Bayview': 22,
        'Nob Hill': 8,
        'Union Square': 12,
        'Chinatown': 11,
        'The Castro': 16,
        'Presidio': 11,
        'Russian Hill': 7
    },
    'Russian Hill': {
        'Bayview': 23,
        'Nob Hill': 5,
        'Union Square': 11,
        'Chinatown': 9,
        'The Castro': 21,
        'Presidio': 14,
        'Pacific Heights': 7
    }
}

best_itinerary = []
best_count = 0

# Check subsets from largest to smallest
for subset_size in range(len(friends), 0, -1):
    # Generate all possible subsets of this size
    for subset in itertools.combinations(friends, subset_size):
        # For each subset, generate all permutations and check if any is feasible
        for perm in itertools.permutations(subset):
            current_time = 9 * 60  # Start at 9:00 AM (540 minutes)
            current_location = 'Bayview'
            itinerary = []
            valid = True
            for friend in perm:
                # Get travel time from current location to friend's location
                destination = friend['location']
                if current_location not in travel_times or destination not in travel_times[current_location]:
                    valid = False
                    break
                travel_time = travel_times[current_location][destination]
                arrival_time = current_time + travel_time

                # Check if the friend's available window can accommodate the meeting
                friend_start = friend['available_start']
                friend_end = friend['available_end']
                required = friend['required_duration']

                # The earliest possible meeting start time is max(arrival_time, friend's start)
                meeting_start = max(arrival_time, friend_start)
                meeting_end = meeting_start + required

                if meeting_end > friend_end:
                    # Can't meet this friend; break and try next permutation
                    valid = False
                    break
                # Add to itinerary
                itinerary.append({
                    'action': 'meet',
                    'location': destination,
                    'person': friend['name'],
                    'start_time': minutes_to_time_str(meeting_start),
                    'end_time': minutes_to_time_str(meeting_end)
                })
                current_time = meeting_end
                current_location = destination
            # After processing all friends in permutation
            if valid:
                # Found a valid itinerary for this subset
                best_count = subset_size
                best_itinerary = itinerary.copy()
                # Output and exit
                result = {"itinerary": best_itinerary}
                print(json.dumps(result, indent=2))
                exit()

# If no friends can be met (unlikely given the constraints)
print(json.dumps({"itinerary": []}))