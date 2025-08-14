import itertools
import json

def minutes_to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

friends = [
    {
        'name': 'Nancy',
        'location': 'Pacific Heights',
        'available_start': 480,  # 8:00 AM
        'available_end': 690,    # 11:30 AM
        'required_duration': 90
    },
    {
        'name': 'Lisa',
        'location': 'Union Square',
        'available_start': 540,  # 9:00 AM
        'available_end': 990,    # 4:30 PM
        'required_duration': 45
    },
    {
        'name': 'Andrew',
        'location': 'Nob Hill',
        'available_start': 690,  # 11:30 AM
        'available_end': 1215,   # 8:15 PM
        'required_duration': 60
    },
    {
        'name': 'Joshua',
        'location': 'Financial District',
        'available_start': 720,  # 12:00 PM
        'available_end': 915,    # 3:15 PM
        'required_duration': 15
    },
    {
        'name': 'John',
        'location': 'Bayview',
        'available_start': 1005, # 4:45 PM
        'available_end': 1290,   # 9:30 PM
        'required_duration': 75
    },
    {
        'name': 'Kenneth',
        'location': 'Richmond District',
        'available_start': 1275, # 9:15 PM
        'available_end': 1320,   # 10:00 PM
        'required_duration': 30
    }
]

travel_times = {
    'Embarcadero': {
        'Richmond District': 21,
        'Union Square': 10,
        'Financial District': 5,
        'Pacific Heights': 11,
        'Nob Hill': 10,
        'Bayview': 21
    },
    'Richmond District': {
        'Embarcadero': 19,
        'Union Square': 21,
        'Financial District': 22,
        'Pacific Heights': 10,
        'Nob Hill': 17,
        'Bayview': 26
    },
    'Union Square': {
        'Embarcadero': 11,
        'Richmond District': 20,
        'Financial District': 9,
        'Pacific Heights': 15,
        'Nob Hill': 9,
        'Bayview': 15
    },
    'Financial District': {
        'Embarcadero': 4,
        'Richmond District': 21,
        'Union Square': 9,
        'Pacific Heights': 13,
        'Nob Hill': 8,
        'Bayview': 19
    },
    'Pacific Heights': {
        'Embarcadero': 10,
        'Richmond District': 12,
        'Union Square': 12,
        'Financial District': 13,
        'Nob Hill': 8,
        'Bayview': 22
    },
    'Nob Hill': {
        'Embarcadero': 9,
        'Richmond District': 14,
        'Union Square': 7,
        'Financial District': 9,
        'Pacific Heights': 8,
        'Bayview': 19
    },
    'Bayview': {
        'Embarcadero': 19,
        'Richmond District': 25,
        'Union Square': 17,
        'Financial District': 19,
        'Pacific Heights': 23,
        'Nob Hill': 20
    }
}

best_itinerary = []
best_length = 0

for subset_size in range(6, 0, -1):
    for subset in itertools.combinations(friends, subset_size):
        for perm in itertools.permutations(subset):
            # Check if permutation is feasible
            current_time = 540  # 9:00 AM
            current_location = 'Embarcadero'
            valid = True
            for friend in perm:
                next_location = friend['location']
                if current_location not in travel_times or next_location not in travel_times[current_location]:
                    valid = False
                    break
                travel_time = travel_times[current_location][next_location]
                arrival_time = current_time + travel_time
                start_time = max(arrival_time, friend['available_start'])
                end_time_meeting = start_time + friend['required_duration']
                if end_time_meeting > friend['available_end']:
                    valid = False
                    break
                current_time = end_time_meeting
                current_location = next_location
            if valid:
                if subset_size > best_length:
                    best_length = subset_size
                    # Re-simulate to collect the details
                    current_time = 540
                    current_location = 'Embarcadero'
                    itinerary = []
                    for friend in perm:
                        next_location = friend['location']
                        travel_time = travel_times[current_location][next_location]
                        arrival_time = current_time + travel_time
                        start_time = max(arrival_time, friend['available_start'])
                        end_time_meeting = start_time + friend['required_duration']
                        # Convert to time strings
                        start_str = minutes_to_time_str(start_time)
                        end_str = minutes_to_time_str(end_time_meeting)
                        itinerary.append({
                            'action': 'meet',
                            'location': next_location,
                            'person': friend['name'],
                            'start_time': start_str,
                            'end_time': end_str
                        })
                        current_time = end_time_meeting
                        current_location = next_location
                    best_itinerary = itinerary
                elif subset_size == best_length:
                    # For simplicity, keep the first one found
                    pass

result = {
    "itinerary": best_itinerary
}

print(json.dumps(result, indent=2))