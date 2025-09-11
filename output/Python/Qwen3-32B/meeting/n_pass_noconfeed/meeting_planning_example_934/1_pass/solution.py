import heapq
import json

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    friends = [
        {
            'name': 'Mary',
            'location': 'Embarcadero',
            'available_start': 20 * 60,
            'available_end': 21 * 60 + 15,
            'duration': 75,
        },
        {
            'name': 'Kenneth',
            'location': 'The Castro',
            'available_start': 11 * 60 + 15,
            'available_end': 19 * 60,
            'duration': 30,
        },
        {
            'name': 'Joseph',
            'location': 'Haight-Ashbury',
            'available_start': 20 * 60,
            'available_end': 22 * 60,
            'duration': 120,
        },
        {
            'name': 'Sarah',
            'location': 'Union Square',
            'available_start': 11 * 60 + 45,
            'available_end': 14 * 60 + 30,
            'duration': 90,
        },
        {
            'name': 'Thomas',
            'location': 'North Beach',
            'available_start': 19 * 60 + 15,
            'available_end': 19 * 60 + 45,
            'duration': 15,
        },
        {
            'name': 'Daniel',
            'location': 'Pacific Heights',
            'available_start': 13 * 60 + 45,
            'available_end': 20 * 60 + 30,
            'duration': 15,
        },
        {
            'name': 'Richard',
            'location': 'Chinatown',
            'available_start': 8 * 60,
            'available_end': 18 * 60 + 45,
            'duration': 30,
        },
        {
            'name': 'Mark',
            'location': 'Golden Gate Park',
            'available_start': 17 * 60 + 30,
            'available_end': 21 * 60 + 30,
            'duration': 120,
        },
        {
            'name': 'David',
            'location': 'Marina District',
            'available_start': 20 * 60,
            'available_end': 21 * 60,
            'duration': 60,
        },
        {
            'name': 'Karen',
            'location': 'Russian Hill',
            'available_start': 13 * 60 + 15,
            'available_end': 18 * 60 + 30,
            'duration': 120,
        },
    ]

    travel_times = {
        'Nob Hill': {
            'Embarcadero': 9, 'The Castro': 17, 'Haight-Ashbury': 13, 'Union Square': 7, 'North Beach': 8,
            'Pacific Heights': 8, 'Chinatown': 6, 'Golden Gate Park': 17, 'Marina District': 11, 'Russian Hill': 5
        },
        'Embarcadero': {
            'Nob Hill': 10, 'The Castro': 25, 'Haight-Ashbury': 21, 'Union Square': 10, 'North Beach': 5,
            'Pacific Heights': 11, 'Chinatown': 7, 'Golden Gate Park': 25, 'Marina District': 12, 'Russian Hill': 8
        },
        'The Castro': {
            'Nob Hill': 16, 'Embarcadero': 22, 'Haight-Ashbury': 6, 'Union Square': 19, 'North Beach': 20,
            'Pacific Heights': 16, 'Chinatown': 22, 'Golden Gate Park': 11, 'Marina District': 21, 'Russian Hill': 18
        },
        'Haight-Ashbury': {
            'Nob Hill': 15, 'Embarcadero': 20, 'The Castro': 6, 'Union Square': 19, 'North Beach': 19,
            'Pacific Heights': 12, 'Chinatown': 19, 'Golden Gate Park': 7, 'Marina District': 17, 'Russian Hill': 17
        },
        'Union Square': {
            'Nob Hill': 9, 'Embarcadero': 11, 'The Castro': 17, 'Haight-Ashbury': 18, 'North Beach': 10,
            'Pacific Heights': 15, 'Chinatown': 7, 'Golden Gate Park': 22, 'Marina District': 18, 'Russian Hill': 13
        },
        'North Beach': {
            'Nob Hill': 7, 'Embarcadero': 6, 'The Castro': 23, 'Haight-Ashbury': 18, 'Union Square': 7,
            'Pacific Heights': 8, 'Chinatown': 6, 'Golden Gate Park': 22, 'Marina District': 9, 'Russian Hill': 4
        },
        'Pacific Heights': {
            'Nob Hill': 8, 'Embarcadero': 10, 'The Castro': 16, 'Haight-Ashbury': 11, 'Union Square': 12,
            'North Beach': 9, 'Chinatown': 11, 'Golden Gate Park': 15, 'Marina District': 6, 'Russian Hill': 7
        },
        'Chinatown': {
            'Nob Hill': 9, 'Embarcadero': 5, 'The Castro': 22, 'Haight-Ashbury': 19, 'Union Square': 7,
            'North Beach': 3, 'Pacific Heights': 10, 'Golden Gate Park': 23, 'Marina District': 12, 'Russian Hill': 7
        },
        'Golden Gate Park': {
            'Nob Hill': 20, 'Embarcadero': 25, 'The Castro': 13, 'Haight-Ashbury': 7, 'Union Square': 22,
            'North Beach': 23, 'Pacific Heights': 16, 'Chinatown': 23, 'Marina District': 16, 'Russian Hill': 19
        },
        'Marina District': {
            'Nob Hill': 12, 'Embarcadero': 14, 'The Castro': 22, 'Haight-Ashbury': 16, 'Union Square': 16,
            'North Beach': 11, 'Pacific Heights': 7, 'Chinatown': 15, 'Golden Gate Park': 18, 'Russian Hill': 8
        },
        'Russian Hill': {
            'Nob Hill': 5, 'Embarcadero': 8, 'The Castro': 21, 'Haight-Ashbury': 17, 'Union Square': 10,
            'North Beach': 5, 'Pacific Heights': 7, 'Chinatown': 9, 'Golden Gate Park': 21, 'Marina District': 7
        },
    }

    initial_time = 9 * 60
    initial_location = 'Nob Hill'
    initial_path = []

    heap = []
    heapq.heappush(heap, (-0, initial_time, initial_location, initial_path))
    best = {}
    best_key = (initial_time, initial_location)
    best[best_key] = 0

    max_path = initial_path

    while heap:
        neg_num_friends, current_time, current_location, path = heapq.heappop(heap)
        current_num_friends = -neg_num_friends

        current_key = (current_time, current_location)
        if best.get(current_key, -1) > current_num_friends:
            continue

        if len(path) > len(max_path):
            max_path = path

        for friend in friends:
            if any(meet['person'] == friend['name'] for meet in path):
                continue

            if current_location not in travel_times or friend['location'] not in travel_times[current_location]:
                continue

            travel_time = travel_times[current_location][friend['location']]
            arrival_time = current_time + travel_time

            meeting_start = max(arrival_time, friend['available_start'])
            meeting_end = meeting_start + friend['duration']

            if meeting_end > friend['available_end']:
                continue

            new_time = meeting_end
            new_location = friend['location']
            new_num_friends = current_num_friends + 1

            start_time_str = minutes_to_time(meeting_start)
            end_time_str = minutes_to_time(meeting_end)
            new_meeting = {
                'action': 'meet',
                'location': friend['location'],
                'person': friend['name'],
                'start_time': start_time_str,
                'end_time': end_time_str,
            }
            new_path = path + [new_meeting]

            new_key = (new_time, new_location)
            if new_key not in best or new_num_friends > best[new_key]:
                best[new_key] = new_num_friends
                heapq.heappush(heap, (-new_num_friends, new_time, new_location, new_path))

    result = {"itinerary": max_path}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()