import json
from copy import deepcopy

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    # Define the travel times
    travel_time = {
        'Chinatown': {
            'Embarcadero': 5,
            'Pacific Heights': 10,
            'Russian Hill': 7,
            'Haight-Ashbury': 19,
            'Golden Gate Park': 23,
            'Fisherman\'s Wharf': 8,
            'Sunset District': 29,
            'The Castro': 22
        },
        'Embarcadero': {
            'Chinatown': 7,
            'Pacific Heights': 11,
            'Russian Hill': 8,
            'Haight-Ashbury': 21,
            'Golden Gate Park': 25,
            'Fisherman\'s Wharf': 6,
            'Sunset District': 30,
            'The Castro': 25
        },
        'Pacific Heights': {
            'Chinatown': 11,
            'Embarcadero': 10,
            'Russian Hill': 7,
            'Haight-Ashbury': 11,
            'Golden Gate Park': 15,
            'Fisherman\'s Wharf': 13,
            'Sunset District': 21,
            'The Castro': 16
        },
        'Russian Hill': {
            'Chinatown': 9,
            'Embarcadero': 8,
            'Pacific Heights': 7,
            'Haight-Ashbury': 17,
            'Golden Gate Park': 21,
            'Fisherman\'s Wharf': 7,
            'Sunset District': 23,
            'The Castro': 21
        },
        'Haight-Ashbury': {
            'Chinatown': 19,
            'Embarcadero': 20,
            'Pacific Heights': 12,
            'Russian Hill': 17,
            'Golden Gate Park': 7,
            'Fisherman\'s Wharf': 23,
            'Sunset District': 15,
            'The Castro': 6
        },
        'Golden Gate Park': {
            'Chinatown': 23,
            'Embarcadero': 25,
            'Pacific Heights': 16,
            'Russian Hill': 19,
            'Haight-Ashbury': 7,
            'Fisherman\'s Wharf': 24,
            'Sunset District': 10,
            'The Castro': 13
        },
        'Fisherman\'s Wharf': {
            'Chinatown': 12,
            'Embarcadero': 8,
            'Pacific Heights': 12,
            'Russian Hill': 7,
            'Haight-Ashbury': 22,
            'Golden Gate Park': 25,
            'Sunset District': 27,
            'The Castro': 27
        },
        'Sunset District': {
            'Chinatown': 30,
            'Embarcadero': 30,
            'Pacific Heights': 21,
            'Russian Hill': 24,
            'Haight-Ashbury': 15,
            'Golden Gate Park': 11,
            'Fisherman\'s Wharf': 29,
            'The Castro': 17
        },
        'The Castro': {
            'Chinatown': 22,
            'Embarcadero': 22,
            'Pacific Heights': 16,
            'Russian Hill': 18,
            'Haight-Ashbury': 6,
            'Golden Gate Park': 11,
            'Fisherman\'s Wharf': 24,
            'Sunset District': 17
        }
    }

    friends = [
        {
            'name': 'Richard',
            'location': 'Embarcadero',
            'earliest': 15 * 60 + 15,  # 15:15
            'latest': 18 * 60 + 45,     # 18:45
            'duration': 90,
        },
        {
            'name': 'Mark',
            'location': 'Pacific Heights',
            'earliest': 15 * 60 + 0,   # 15:00
            'latest': 17 * 60 + 0,     # 17:00
            'duration': 45,
        },
        {
            'name': 'Matthew',
            'location': 'Russian Hill',
            'earliest': 17 * 60 + 30,  # 17:30
            'latest': 21 * 60 + 0,     # 21:00
            'duration': 90,
        },
        {
            'name': 'Rebecca',
            'location': 'Haight-Ashbury',
            'earliest': 14 * 60 + 45,  # 14:45
            'latest': 18 * 60 + 0,     # 18:00
            'duration': 60,
        },
        {
            'name': 'Melissa',
            'location': 'Golden Gate Park',
            'earliest': 13 * 60 + 45,  # 13:45
            'latest': 17 * 60 + 30,    # 17:30
            'duration': 90,
        },
        {
            'name': 'Margaret',
            'location': 'Fisherman\'s Wharf',
            'earliest': 14 * 60 + 45,  # 14:45
            'latest': 20 * 60 + 15,    # 20:15
            'duration': 15,
        },
        {
            'name': 'Emily',
            'location': 'Sunset District',
            'earliest': 15 * 60 + 45,  # 15:45
            'latest': 17 * 60 + 0,     # 17:00
            'duration': 45,
        },
        {
            'name': 'George',
            'location': 'The Castro',
            'earliest': 14 * 60 + 0,   # 14:00
            'latest': 16 * 60 + 15,    # 16:15
            'duration': 75,
        },
    ]

    best_path = []

    def backtrack(current_location, current_time, visited, path):
        nonlocal best_path

        # Update best_path if current path is better
        if len(path) > len(best_path):
            best_path = deepcopy(path)

        # Try all unvisited friends
        for i in range(len(friends)):
            if i in visited:
                continue

            friend = friends[i]
            # Get travel time
            loc = friend['location']
            travel = travel_time[current_location].get(loc)
            if travel is None:
                continue  # Should not happen in this problem

            arrival_time = current_time + travel

            # Check if meeting is possible
            earliest = friend['earliest']
            latest = friend['latest']
            duration = friend['duration']

            start_time = max(arrival_time, earliest)
            end_time = start_time + duration

            if end_time > latest:
                continue  # Not enough time

            # Add to path and visited
            visited.add(i)
            path.append({
                'action': 'meet',
                'location': loc,
                'person': friend['name'],
                'start_time': start_time,
                'end_time': end_time
            })

            # Recurse
            backtrack(loc, end_time, visited, path)

            # Backtrack
            path.pop()
            visited.remove(i)

    # Initial call: start at Chinatown at 9:00 AM (540 minutes)
    initial_visited = set()
    initial_path = []
    backtrack('Chinatown', 9 * 60, initial_visited, initial_path)

    # Convert best_path to the required JSON format
    itinerary = []
    for meeting in best_path:
        start_str = minutes_to_time(meeting['start_time'])
        end_str = minutes_to_time(meeting['end_time'])
        itinerary.append({
            'action': 'meet',
            'location': meeting['location'],
            'person': meeting['person'],
            'start_time': start_str,
            'end_time': end_str
        })

    result = {'itinerary': itinerary}
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()