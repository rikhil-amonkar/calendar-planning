import itertools
import json

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def is_feasible(perm, travel_times):
    current_time = 9 * 60  # 9:00 AM
    current_location = 'North Beach'
    itinerary = []

    for friend in perm:
        dest_location = friend['location']
        travel_time = travel_times[current_location][dest_location]
        arrival_time = current_time + travel_time

        friend_start = time_to_minutes(friend['available_start'])
        friend_end = time_to_minutes(friend['available_end'])
        required_duration = friend['required_duration']

        start_time = max(arrival_time, friend_start)
        end_time = start_time + required_duration

        if end_time > friend_end:
            return None  # Not feasible

        # Add to itinerary
        itinerary.append({
            'action': 'meet',
            'location': dest_location,
            'person': friend['name'],
            'start_time': minutes_to_time(start_time),
            'end_time': minutes_to_time(end_time)
        })

        current_time = end_time
        current_location = dest_location

    return itinerary

def main():
    friends = [
        {
            'name': 'James',
            'location': 'Pacific Heights',
            'available_start': '20:00',
            'available_end': '22:00',
            'required_duration': 120
        },
        {
            'name': 'Robert',
            'location': 'Chinatown',
            'available_start': '12:15',
            'available_end': '16:45',
            'required_duration': 90
        },
        {
            'name': 'Jeffrey',
            'location': 'Union Square',
            'available_start': '9:30',
            'available_end': '15:30',
            'required_duration': 120
        },
        {
            'name': 'Carol',
            'location': 'Mission District',
            'available_start': '18:15',
            'available_end': '21:15',
            'required_duration': 15
        },
        {
            'name': 'Mark',
            'location': 'Golden Gate Park',
            'available_start': '11:30',
            'available_end': '17:45',
            'required_duration': 15
        },
        {
            'name': 'Sandra',
            'location': 'Nob Hill',
            'available_start': '8:00',
            'available_end': '15:30',
            'required_duration': 15
        }
    ]

    travel_times = {
        'North Beach': {
            'Pacific Heights': 8,
            'Chinatown': 6,
            'Union Square': 7,
            'Mission District': 18,
            'Golden Gate Park': 22,
            'Nob Hill': 7
        },
        'Pacific Heights': {
            'North Beach': 9,
            'Chinatown': 11,
            'Union Square': 12,
            'Mission District': 15,
            'Golden Gate Park': 15,
            'Nob Hill': 8
        },
        'Chinatown': {
            'North Beach': 3,
            'Pacific Heights': 10,
            'Union Square': 7,
            'Mission District': 18,
            'Golden Gate Park': 23,
            'Nob Hill': 8
        },
        'Union Square': {
            'North Beach': 10,
            'Pacific Heights': 15,
            'Chinatown': 7,
            'Mission District': 14,
            'Golden Gate Park': 22,
            'Nob Hill': 9
        },
        'Mission District': {
            'North Beach': 17,
            'Pacific Heights': 16,
            'Chinatown': 16,
            'Union Square': 15,
            'Golden Gate Park': 17,
            'Nob Hill': 12
        },
        'Golden Gate Park': {
            'North Beach': 24,
            'Pacific Heights': 16,
            'Chinatown': 23,
            'Union Square': 22,
            'Mission District': 17,
            'Nob Hill': 20
        },
        'Nob Hill': {
            'North Beach': 8,
            'Pacific Heights': 8,
            'Chinatown': 6,
            'Union Square': 7,
            'Mission District': 13,
            'Golden Gate Park': 17
        }
    }

    # Try all subset sizes from largest to smallest
    for subset_size in range(len(friends), 0, -1):
        # Generate all combinations of friends of this size
        for subset in itertools.combinations(friends, subset_size):
            # Generate all permutations of this subset
            for perm in itertools.permutations(subset):
                itinerary = is_feasible(perm, travel_times)
                if itinerary is not None:
                    # Found a valid itinerary
                    result = {
                        "itinerary": itinerary
                    }
                    print(json.dumps(result, indent=2))
                    return

    # If no itinerary found
    print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()