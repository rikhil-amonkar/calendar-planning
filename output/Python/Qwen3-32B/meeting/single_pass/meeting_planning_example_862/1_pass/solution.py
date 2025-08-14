import json

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Define friends
friends = [
    {
        'name': 'Laura',
        'location': 'Alamo Square',
        'available_start': 14 * 60 + 30,
        'available_end': 16 * 60 + 15,
        'required_duration': 75
    },
    {
        'name': 'Brian',
        'location': 'Presidio',
        'available_start': 10 * 60 + 15,
        'available_end': 17 * 60 + 0,
        'required_duration': 30
    },
    {
        'name': 'Karen',
        'location': 'Russian Hill',
        'available_start': 18 * 60 + 0,
        'available_end': 20 * 60 + 15,
        'required_duration': 90
    },
    {
        'name': 'Stephanie',
        'location': 'North Beach',
        'available_start': 10 * 60 + 15,
        'available_end': 16 * 60 + 0,
        'required_duration': 75
    },
    {
        'name': 'Helen',
        'location': 'Golden Gate Park',
        'available_start': 11 * 60 + 30,
        'available_end': 21 * 60 + 45,
        'required_duration': 120
    },
    {
        'name': 'Sandra',
        'location': 'Richmond District',
        'available_start': 8 * 60 + 0,
        'available_end': 15 * 60 + 15,
        'required_duration': 30
    },
    {
        'name': 'Mary',
        'location': 'Embarcadero',
        'available_start': 16 * 60 + 45,
        'available_end': 18 * 60 + 45,
        'required_duration': 120
    },
    {
        'name': 'Deborah',
        'location': 'Financial District',
        'available_start': 19 * 60 + 0,
        'available_end': 20 * 60 + 45,
        'required_duration': 105
    },
    {
        'name': 'Elizabeth',
        'location': 'Marina District',
        'available_start': 8 * 60 + 30,
        'available_end': 13 * 60 + 15,
        'required_duration': 105
    }
]

# Define travel times between locations
travel_times = {
    'Mission District': {
        'Alamo Square': 11,
        'Presidio': 25,
        'Russian Hill': 15,
        'North Beach': 17,
        'Golden Gate Park': 17,
        'Richmond District': 20,
        'Embarcadero': 19,
        'Financial District': 15,
        'Marina District': 19,
    },
    'Alamo Square': {
        'Mission District': 10,
        'Presidio': 17,
        'Russian Hill': 13,
        'North Beach': 15,
        'Golden Gate Park': 9,
        'Richmond District': 11,
        'Embarcadero': 16,
        'Financial District': 17,
        'Marina District': 15,
    },
    'Presidio': {
        'Mission District': 26,
        'Alamo Square': 19,
        'Russian Hill': 14,
        'North Beach': 18,
        'Golden Gate Park': 12,
        'Richmond District': 7,
        'Embarcadero': 20,
        'Financial District': 23,
        'Marina District': 11,
    },
    'Russian Hill': {
        'Mission District': 16,
        'Alamo Square': 15,
        'Presidio': 14,
        'North Beach': 5,
        'Golden Gate Park': 21,
        'Richmond District': 14,
        'Embarcadero': 8,
        'Financial District': 11,
        'Marina District': 7,
    },
    'North Beach': {
        'Mission District': 18,
        'Alamo Square': 16,
        'Presidio': 17,
        'Russian Hill': 4,
        'Golden Gate Park': 22,
        'Richmond District': 18,
        'Embarcadero': 6,
        'Financial District': 8,
        'Marina District': 9,
    },
    'Golden Gate Park': {
        'Mission District': 17,
        'Alamo Square': 9,
        'Presidio': 11,
        'Russian Hill': 19,
        'North Beach': 23,
        'Richmond District': 7,
        'Embarcadero': 25,
        'Financial District': 26,
        'Marina District': 16,
    },
    'Richmond District': {
        'Mission District': 20,
        'Alamo Square': 13,
        'Presidio': 7,
        'Russian Hill': 13,
        'North Beach': 17,
        'Golden Gate Park': 9,
        'Embarcadero': 19,
        'Financial District': 22,
        'Marina District': 9,
    },
    'Embarcadero': {
        'Mission District': 20,
        'Alamo Square': 19,
        'Presidio': 20,
        'Russian Hill': 8,
        'North Beach': 5,
        'Golden Gate Park': 25,
        'Richmond District': 21,
        'Financial District': 5,
        'Marina District': 14,
    },
    'Financial District': {
        'Mission District': 17,
        'Alamo Square': 17,
        'Presidio': 22,
        'Russian Hill': 11,
        'North Beach': 7,
        'Golden Gate Park': 23,
        'Richmond District': 21,
        'Embarcadero': 4,
        'Marina District': 15,
    },
    'Marina District': {
        'Mission District': 20,
        'Alamo Square': 15,
        'Presidio': 10,
        'Russian Hill': 8,
        'North Beach': 11,
        'Golden Gate Park': 18,
        'Richmond District': 11,
        'Embarcadero': 14,
        'Financial District': 17,
    }
}

best_itinerary = []

def backtrack(current_location, current_time, visited_indices, path):
    global best_itinerary

    # Update best itinerary if current path is better
    if len(path) > len(best_itinerary):
        best_itinerary = path.copy()

    # Try all friends not yet visited
    for i in range(len(friends)):
        if i not in visited_indices:
            friend = friends[i]
            # Calculate arrival time
            travel_time = travel_times[current_location][friend['location']]
            arrival_time = current_time + travel_time

            # Determine meeting start time and end time
            start_meeting_time = max(arrival_time, friend['available_start'])
            end_meeting_time = start_meeting_time + friend['required_duration']

            if end_meeting_time <= friend['available_end']:
                # Add to path and visited
                visited_indices.add(i)
                path.append({
                    'action': 'meet',
                    'location': friend['location'],
                    'person': friend['name'],
                    'start_time': minutes_to_time(start_meeting_time),
                    'end_time': minutes_to_time(end_meeting_time)
                })

                # Recurse
                backtrack(friend['location'], end_meeting_time, visited_indices, path)

                # Backtrack
                path.pop()
                visited_indices.remove(i)

# Initial call
visited_indices = set()
path = []
backtrack('Mission District', 9 * 60, visited_indices, path)

# Output as JSON
result = {
    "itinerary": best_itinerary
}

print(json.dumps(result, indent=2))