import itertools
import json

def minutes_to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Define friends and their constraints
friends = [
    {
        'name': 'John',
        'location': 'Pacific Heights',
        'available_start': 9 * 60,  # 9:00 AM
        'available_end': 13.5 * 60,  # 1:30 PM
        'required_duration': 15
    },
    {
        'name': 'Steven',
        'location': 'North Beach',
        'available_start': 13.5 * 60,  # 1:30 PM
        'available_end': 22 * 60,  # 10:00 PM
        'required_duration': 45
    },
    {
        'name': 'Barbara',
        'location': "Fisherman's Wharf",
        'available_start': 18 * 60,  # 6:00 PM
        'available_end': 21.5 * 60,  # 9:30 PM
        'required_duration': 30
    }
]

# Define travel times between locations
travel_times = {
    'Nob Hill': {
        'Presidio': 17,
        'North Beach': 8,
        'Fisherman\'s Wharf': 11,
        'Pacific Heights': 8
    },
    'Presidio': {
        'Nob Hill': 18,
        'North Beach': 18,
        'Fisherman\'s Wharf': 19,
        'Pacific Heights': 11
    },
    'North Beach': {
        'Nob Hill': 7,
        'Presidio': 17,
        'Fisherman\'s Wharf': 5,
        'Pacific Heights': 8
    },
    "Fisherman's Wharf": {
        'Nob Hill': 11,
        'Presidio': 17,
        'North Beach': 6,
        'Pacific Heights': 13
    },
    'Pacific Heights': {
        'Nob Hill': 8,
        'Presidio': 11,
        'North Beach': 9,
        "Fisherman's Wharf": 13
    }
}

# Generate all permutations of friends and find the best itinerary
best_itinerary = []
max_friends = 0

for perm in itertools.permutations(friends):
    current_time = 9 * 60  # Start at 9:00 AM
    current_location = 'Nob Hill'
    valid = True
    meetings = []
    for friend in perm:
        # Check if travel time exists
        if current_location not in travel_times or friend['location'] not in travel_times[current_location]:
            valid = False
            break
        travel_time = travel_times[current_location][friend['location']]
        arrival_time = current_time + travel_time
        # Determine the start time of the meeting
        start_time = max(arrival_time, friend['available_start'])
        end_time = start_time + friend['required_duration']
        # Check if the meeting fits within the available time
        if end_time > friend['available_end']:
            valid = False
            break
        # Record the meeting
        meetings.append((friend, start_time, end_time))
        # Update current time and location
        current_time = end_time
        current_location = friend['location']
    if valid:
        if len(meetings) > max_friends:
            max_friends = len(meetings)
            best_itinerary = meetings
        elif len(meetings) == max_friends and max_friends > 0:
            # Keep the first valid itinerary found with max friends
            pass

# Convert best itinerary to the required JSON format
itinerary = []
for meeting in best_itinerary:
    friend = meeting[0]
    start_time = minutes_to_time_str(meeting[1])
    end_time = minutes_to_time_str(meeting[2])
    itinerary.append({
        "action": "meet",
        "location": friend['location'],
        "person": friend['name'],
        "start_time": start_time,
        "end_time": end_time
    })

# Output as JSON
result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))