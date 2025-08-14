import json

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    friends = [
        {
            'name': 'Betty',
            'location': 'Russian Hill',
            'available_start': 420,  # 7:00 AM
            'available_end': 1005,   # 4:45 PM
            'required_duration': 105
        },
        {
            'name': 'Melissa',
            'location': 'Alamo Square',
            'available_start': 570,  # 9:30 AM
            'available_end': 1035,   # 5:15 PM
            'required_duration': 105
        },
        {
            'name': 'Joshua',
            'location': 'Haight-Ashbury',
            'available_start': 735,  # 12:15 PM
            'available_end': 1140,   # 7:00 PM
            'required_duration': 90
        },
        {
            'name': 'Jeffrey',
            'location': 'Marina District',
            'available_start': 735,  # 12:15 PM
            'available_end': 1080,   # 6:00 PM
            'required_duration': 45
        },
        {
            'name': 'James',
            'location': 'Bayview',
            'available_start': 450,  # 7:30 AM
            'available_end': 1200,   # 8:00 PM
            'required_duration': 90
        },
        {
            'name': 'Anthony',
            'location': 'Chinatown',
            'available_start': 705,  # 11:45 AM
            'available_end': 810,    # 1:30 PM
            'required_duration': 75
        },
        {
            'name': 'Timothy',
            'location': 'Presidio',
            'available_start': 750,  # 12:30 PM
            'available_end': 885,    # 2:45 PM
            'required_duration': 90
        },
        {
            'name': 'Emily',
            'location': 'Sunset District',
            'available_start': 1170, # 7:30 PM
            'available_end': 1290,   # 9:30 PM
            'required_duration': 120
        }
    ]
    travel_times = {
        'Union Square': {
            'Russian Hill': 13,
            'Alamo Square': 15,
            'Haight-Ashbury': 18,
            'Marina District': 18,
            'Bayview': 15,
            'Chinatown': 7,
            'Presidio': 24,
            'Sunset District': 27,
        },
        'Russian Hill': {
            'Union Square': 10,
            'Alamo Square': 15,
            'Haight-Ashbury': 17,
            'Marina District': 7,
            'Bayview': 23,
            'Chinatown': 9,
            'Presidio': 14,
            'Sunset District': 23,
        },
        'Alamo Square': {
            'Union Square': 14,
            'Russian Hill': 13,
            'Haight-Ashbury': 5,
            'Marina District': 15,
            'Bayview': 16,
            'Chinatown': 15,
            'Presidio': 17,
            'Sunset District': 16,
        },
        'Haight-Ashbury': {
            'Union Square': 19,
            'Russian Hill': 17,
            'Alamo Square': 5,
            'Marina District': 17,
            'Bayview': 18,
            'Chinatown': 19,
            'Presidio': 15,
            'Sunset District': 15,
        },
        'Marina District': {
            'Union Square': 16,
            'Russian Hill': 8,
            'Alamo Square': 15,
            'Haight-Ashbury': 16,
            'Bayview': 27,
            'Chinatown': 15,
            'Presidio': 10,
            'Sunset District': 19,
        },
        'Bayview': {
            'Union Square': 18,
            'Russian Hill': 23,
            'Alamo Square': 16,
            'Haight-Ashbury': 19,
            'Marina District': 27,
            'Chinatown': 19,
            'Presidio': 32,
            'Sunset District': 23,
        },
        'Chinatown': {
            'Union Square': 7,
            'Russian Hill': 7,
            'Alamo Square': 17,
            'Haight-Ashbury': 19,
            'Marina District': 12,
            'Bayview': 20,
            'Presidio': 19,
            'Sunset District': 29,
        },
        'Presidio': {
            'Union Square': 22,
            'Russian Hill': 14,
            'Alamo Square': 19,
            'Haight-Ashbury': 15,
            'Marina District': 11,
            'Bayview': 31,
            'Chinatown': 21,
            'Sunset District': 16,
        },
        'Sunset District': {
            'Union Square': 30,
            'Russian Hill': 24,
            'Alamo Square': 17,
            'Haight-Ashbury': 15,
            'Marina District': 21,
            'Bayview': 22,
            'Chinatown': 30,
            'Presidio': 16,
        },
    }

    best_solution = [ [] ]  # list containing the best path as a list of indices

    def backtrack(current_time, current_location, path, remaining):
        # Update best_solution if current path is better
        if len(path) > len(best_solution[0]):
            best_solution[0] = path.copy()
        # Try all possible next friends
        for friend_idx in list(remaining):  # iterate over a copy to avoid modification during iteration
            friend = friends[friend_idx]
            # Calculate travel time
            travel_time = travel_times[current_location][friend['location']]
            arrival_time = current_time + travel_time
            meeting_start = max(arrival_time, friend['available_start'])
            meeting_end = meeting_start + friend['required_duration']
            # Check if meeting can be scheduled
            if meeting_end > friend['available_end']:
                continue
            # Proceed with this friend
            new_remaining = remaining.copy()
            new_remaining.remove(friend_idx)
            new_path = path.copy()
            new_path.append(friend_idx)
            # Recursive call
            backtrack(meeting_end, friend['location'], new_path, new_remaining)

    # Initial call
    initial_time = 540  # 9:00 AM
    initial_location = 'Union Square'
    initial_path = []
    initial_remaining = set(range(len(friends)))
    backtrack(initial_time, initial_location, initial_path, initial_remaining)

    # Generate the itinerary from best_solution
    best_indices = best_solution[0]
    current_time = 540
    current_location = 'Union Square'
    itinerary = []
    for idx in best_indices:
        friend = friends[idx]
        travel_time = travel_times[current_location][friend['location']]
        arrival_time = current_time + travel_time
        meeting_start = max(arrival_time, friend['available_start'])
        meeting_end = meeting_start + friend['required_duration']
        # Append to itinerary
        itinerary.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': minutes_to_time(meeting_start),
            'end_time': minutes_to_time(meeting_end)
        })
        current_time = meeting_end
        current_location = friend['location']

    # Output as JSON
    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()