import json

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

friends = [
    {
        'name': 'William',
        'location': 'Alamo Square',
        'available_start': 915,
        'available_end': 1035,
        'required_duration': 60
    },
    {
        'name': 'Joshua',
        'location': 'Richmond District',
        'available_start': 420,
        'available_end': 1200,
        'required_duration': 15
    },
    {
        'name': 'Joseph',
        'location': 'Financial District',
        'available_start': 675,
        'available_end': 810,
        'required_duration': 15
    },
    {
        'name': 'David',
        'location': 'Union Square',
        'available_start': 1005,
        'available_end': 1155,
        'required_duration': 45
    },
    {
        'name': 'Brian',
        'location': "Fisherman's Wharf",
        'available_start': 825,
        'available_end': 1245,
        'required_duration': 105
    },
    {
        'name': 'Karen',
        'location': 'Marina District',
        'available_start': 690,
        'available_end': 1110,
        'required_duration': 15
    },
    {
        'name': 'Anthony',
        'location': 'Haight-Ashbury',
        'available_start': 435,
        'available_end': 630,
        'required_duration': 30
    },
    {
        'name': 'Matthew',
        'location': 'Mission District',
        'available_start': 1035,
        'available_end': 1155,
        'required_duration': 120
    },
    {
        'name': 'Helen',
        'location': 'Pacific Heights',
        'available_start': 480,
        'available_end': 720,
        'required_duration': 75
    },
    {
        'name': 'Jeffrey',
        'location': 'Golden Gate Park',
        'available_start': 1140,
        'available_end': 1290,
        'required_duration': 60
    }
]

travel_times = {
    'The Castro': {
        'Alamo Square': 8,
        'Richmond District': 16,
        'Financial District': 21,
        'Union Square': 19,
        "Fisherman's Wharf": 24,
        'Marina District': 21,
        'Haight-Ashbury': 6,
        'Mission District': 7,
        'Pacific Heights': 16,
        'Golden Gate Park': 11,
    },
    'Alamo Square': {
        'The Castro': 8,
        'Richmond District': 11,
        'Financial District': 17,
        'Union Square': 14,
        "Fisherman's Wharf": 19,
        'Marina District': 15,
        'Haight-Ashbury': 5,
        'Mission District': 10,
        'Pacific Heights': 10,
        'Golden Gate Park': 9,
    },
    'Richmond District': {
        'The Castro': 16,
        'Alamo Square': 11,
        'Financial District': 22,
        'Union Square': 21,
        "Fisherman's Wharf": 18,
        'Marina District': 9,
        'Haight-Ashbury': 10,
        'Mission District': 20,
        'Pacific Heights': 10,
        'Golden Gate Park': 9,
    },
    'Financial District': {
        'The Castro': 20,
        'Alamo Square': 17,
        'Richmond District': 22,
        'Union Square': 9,
        "Fisherman's Wharf": 10,
        'Marina District': 15,
        'Haight-Ashbury': 19,
        'Mission District': 17,
        'Pacific Heights': 13,
        'Golden Gate Park': 23,
    },
    'Union Square': {
        'The Castro': 17,
        'Alamo Square': 14,
        'Richmond District': 21,
        'Financial District': 9,
        "Fisherman's Wharf": 15,
        'Marina District': 18,
        'Haight-Ashbury': 18,
        'Mission District': 14,
        'Pacific Heights': 15,
        'Golden Gate Park': 22,
    },
    "Fisherman's Wharf": {
        'The Castro': 24,
        'Alamo Square': 19,
        'Richmond District': 18,
        'Financial District': 10,
        'Union Square': 13,
        'Marina District': 9,
        'Haight-Ashbury': 22,
        'Mission District': 22,
        'Pacific Heights': 12,
        'Golden Gate Park': 25,
    },
    'Marina District': {
        'The Castro': 21,
        'Alamo Square': 15,
        'Richmond District': 9,
        'Financial District': 15,
        'Union Square': 16,
        "Fisherman's Wharf": 9,
        'Haight-Ashbury': 16,
        'Mission District': 20,
        'Pacific Heights': 7,
        'Golden Gate Park': 18,
    },
    'Haight-Ashbury': {
        'The Castro': 6,
        'Alamo Square': 5,
        'Richmond District': 10,
        'Financial District': 19,
        'Union Square': 18,
        "Fisherman's Wharf": 22,
        'Marina District': 16,
        'Mission District': 11,
        'Pacific Heights': 12,
        'Golden Gate Park': 7,
    },
    'Mission District': {
        'The Castro': 7,
        'Alamo Square': 10,
        'Richmond District': 20,
        'Financial District': 17,
        'Union Square': 14,
        "Fisherman's Wharf": 22,
        'Marina District': 20,
        'Haight-Ashbury': 11,
        'Pacific Heights': 16,
        'Golden Gate Park': 17,
    },
    'Pacific Heights': {
        'The Castro': 16,
        'Alamo Square': 10,
        'Richmond District': 12,
        'Financial District': 13,
        'Union Square': 12,
        "Fisherman's Wharf": 13,
        'Marina District': 6,
        'Haight-Ashbury': 11,
        'Mission District': 15,
        'Golden Gate Park': 15,
    },
    'Golden Gate Park': {
        'The Castro': 11,
        'Alamo Square': 9,
        'Richmond District': 7,
        'Financial District': 23,
        'Union Square': 22,
        "Fisherman's Wharf": 24,
        'Marina District': 16,
        'Haight-Ashbury': 7,
        'Mission District': 17,
        'Pacific Heights': 16,
    },
}

# Initialize variables
current_time = 9 * 60  # 9:00 AM in minutes since midnight
current_location = 'The Castro'
unvisited = friends.copy()
itinerary = []

while True:
    feasible_next = []
    for friend in unvisited:
        # Get travel time from current location to friend's location
        travel_time = travel_times[current_location].get(friend['location'], None)
        if travel_time is None:
            continue  # Skip if travel time is not available (shouldn't happen with given data)
        
        arrival_time = current_time + travel_time
        available_start = friend['available_start']
        required_duration = friend['required_duration']
        available_end = friend['available_end']
        
        # Calculate earliest possible start time for the meeting
        earliest_start = max(arrival_time, available_start)
        
        # Check if meeting can fit in available time
        if earliest_start + required_duration <= available_end:
            feasible_next.append( (friend, earliest_start + required_duration) )
    
    if not feasible_next:
        break  # No more friends can be visited
    
    # Choose the friend with the earliest end time
    chosen_friend, chosen_end = min(feasible_next, key=lambda x: x[1])
    
    # Calculate the actual start time (max of arrival time and available start)
    travel_time_to_friend = travel_times[current_location][chosen_friend['location']]
    arrival_time_to_friend = current_time + travel_time_to_friend
    start_time_minutes = max(arrival_time_to_friend, chosen_friend['available_start'])
    
    # Add to itinerary
    itinerary.append({
        'action': 'meet',
        'location': chosen_friend['location'],
        'person': chosen_friend['name'],
        'start_time': minutes_to_time(start_time_minutes),
        'end_time': minutes_to_time(chosen_end)
    })
    
    # Update current time and location
    current_time = chosen_end
    current_location = chosen_friend['location']
    
    # Remove chosen friend from unvisited
    unvisited.remove(chosen_friend)

# Output the result as JSON
result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))