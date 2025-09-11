import copy
import json

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    friends = [
        {
            'name': 'Emily',
            'location': 'Pacific Heights',
            'available_start': 555,
            'available_end': 825,
            'required_duration': 120
        },
        {
            'name': 'Helen',
            'location': 'North Beach',
            'available_start': 825,
            'available_end': 1125,
            'required_duration': 30
        },
        {
            'name': 'Kimberly',
            'location': 'Golden Gate Park',
            'available_start': 1125,
            'available_end': 1275,
            'required_duration': 75
        },
        {
            'name': 'James',
            'location': 'Embarcadero',
            'available_start': 630,
            'available_end': 690,
            'required_duration': 30
        },
        {
            'name': 'Linda',
            'location': 'Haight-Ashbury',
            'available_start': 450,
            'available_end': 1155,
            'required_duration': 15
        },
        {
            'name': 'Paul',
            'location': 'Fisherman\'s Wharf',
            'available_start': 885,
            'available_end': 1125,
            'required_duration': 90
        },
        {
            'name': 'Anthony',
            'location': 'Mission District',
            'available_start': 480,
            'available_end': 885,
            'required_duration': 105
        },
        {
            'name': 'Nancy',
            'location': 'Alamo Square',
            'available_start': 510,
            'available_end': 825,
            'required_duration': 120
        },
        {
            'name': 'William',
            'location': 'Bayview',
            'available_start': 1050,
            'available_end': 1230,
            'required_duration': 120
        },
        {
            'name': 'Margaret',
            'location': 'Richmond District',
            'available_start': 915,
            'available_end': 1095,
            'required_duration': 45
        }
    ]

    travel_times = {
        'Russian Hill': {
            'Pacific Heights': 7,
            'North Beach': 5,
            'Golden Gate Park': 21,
            'Embarcadero': 8,
            'Haight-Ashbury': 17,
            'Fisherman\'s Wharf': 7,
            'Mission District': 16,
            'Alamo Square': 15,
            'Bayview': 23,
            'Richmond District': 14
        },
        'Pacific Heights': {
            'Russian Hill': 7,
            'North Beach': 9,
            'Golden Gate Park': 15,
            'Embarcadero': 10,
            'Haight-Ashbury': 11,
            'Fisherman\'s Wharf': 13,
            'Mission District': 15,
            'Alamo Square': 10,
            'Bayview': 22,
            'Richmond District': 12
        },
        'North Beach': {
            'Russian Hill': 4,
            'Pacific Heights': 8,
            'Golden Gate Park': 22,
            'Embarcadero': 6,
            'Haight-Ashbury': 18,
            'Fisherman\'s Wharf': 5,
            'Mission District': 18,
            'Alamo Square': 16,
            'Bayview': 25,
            'Richmond District': 18
        },
        'Golden Gate Park': {
            'Russian Hill': 19,
            'Pacific Heights': 16,
            'North Beach': 23,
            'Embarcadero': 25,
            'Haight-Ashbury': 7,
            'Fisherman\'s Wharf': 24,
            'Mission District': 17,
            'Alamo Square': 9,
            'Bayview': 23,
            'Richmond District': 7
        },
        'Embarcadero': {
            'Russian Hill': 8,
            'Pacific Heights': 11,
            'North Beach': 5,
            'Golden Gate Park': 25,
            'Haight-Ashbury': 21,
            'Fisherman\'s Wharf': 6,
            'Mission District': 20,
            'Alamo Square': 19,
            'Bayview': 21,
            'Richmond District': 21
        },
        'Haight-Ashbury': {
            'Russian Hill': 17,
            'Pacific Heights': 12,
            'North Beach': 19,
            'Golden Gate Park': 7,
            'Embarcadero': 20,
            'Fisherman\'s Wharf': 23,
            'Mission District': 11,
            'Alamo Square': 5,
            'Bayview': 18,
            'Richmond District': 10
        },
        "Fisherman's Wharf": {
            'Russian Hill': 7,
            'Pacific Heights': 12,
            'North Beach': 6,
            'Golden Gate Park': 25,
            'Embarcadero': 8,
            'Haight-Ashbury': 22,
            'Mission District': 22,
            'Alamo Square': 21,
            'Bayview': 26,
            'Richmond District': 18
        },
        'Mission District': {
            'Russian Hill': 15,
            'Pacific Heights': 16,
            'North Beach': 17,
            'Golden Gate Park': 17,
            'Embarcadero': 19,
            'Haight-Ashbury': 12,
            'Fisherman\'s Wharf': 22,
            'Alamo Square': 11,
            'Bayview': 14,
            'Richmond District': 20
        },
        'Alamo Square': {
            'Russian Hill': 13,
            'Pacific Heights': 10,
            'North Beach': 15,
            'Golden Gate Park': 9,
            'Embarcadero': 16,
            'Haight-Ashbury': 5,
            'Fisherman\'s Wharf': 19,
            'Mission District': 10,
            'Bayview': 16,
            'Richmond District': 11
        },
        'Bayview': {
            'Russian Hill': 23,
            'Pacific Heights': 23,
            'North Beach': 22,
            'Golden Gate Park': 22,
            'Embarcadero': 19,
            'Haight-Ashbury': 19,
            'Fisherman\'s Wharf': 25,
            'Mission District': 13,
            'Alamo Square': 16,
            'Richmond District': 25
        },
        'Richmond District': {
            'Russian Hill': 13,
            'Pacific Heights': 10,
            'North Beach': 17,
            'Golden Gate Park': 9,
            'Embarcadero': 19,
            'Haight-Ashbury': 10,
            'Fisherman\'s Wharf': 18,
            'Mission District': 20,
            'Alamo Square': 13,
            'Bayview': 27
        }
    }

    best_path = []

    def backtrack(current_time, current_location, visited, path):
        nonlocal best_path

        if len(path) > len(best_path):
            best_path = copy.deepcopy(path)

        for i in range(len(friends)):
            if i in visited:
                continue
            friend = friends[i]
            location = friend['location']
            available_start = friend['available_start']
            available_end = friend['available_end']
            required_duration = friend['required_duration']

            if current_location not in travel_times or location not in travel_times[current_location]:
                continue
            travel_time = travel_times[current_location][location]

            arrival_time = current_time + travel_time

            if arrival_time > available_end:
                continue

            start_time = max(arrival_time, available_start)
            end_time = start_time + required_duration

            if end_time > available_end:
                continue

            new_visited = visited.copy()
            new_visited.add(i)
            new_path = copy.deepcopy(path)
            new_path.append({
                'action': 'meet',
                'location': location,
                'person': friend['name'],
                'start_time': minutes_to_time(start_time),
                'end_time': minutes_to_time(end_time)
            })

            backtrack(end_time, location, new_visited, new_path)

    backtrack(540, 'Russian Hill', set(), [])

    print(json.dumps({"itinerary": best_path}))

if __name__ == "__main__":
    main()