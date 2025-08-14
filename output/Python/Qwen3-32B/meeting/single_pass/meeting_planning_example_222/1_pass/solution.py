import itertools
import json

def minutes_to_time_str(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

def main():
    friends = [
        {
            'name': 'Helen',
            'location': 'North Beach',
            'available_start': 420,  # 7:00 AM
            'available_end': 1005,   # 4:45 PM
            'required_duration': 120
        },
        {
            'name': 'Kimberly',
            'location': "Fisherman's Wharf",
            'available_start': 990,  # 4:30 PM
            'available_end': 1050,   # 9:00 PM
            'required_duration': 45
        },
        {
            'name': 'Patricia',
            'location': 'Bayview',
            'available_start': 1080,  # 6:00 PM
            'available_end': 1275,    # 9:15 PM
            'required_duration': 120
        }
    ]

    travel_times = {
        'Nob Hill': {
            'North Beach': 8,
            "Fisherman's Wharf": 11,
            'Bayview': 19
        },
        'North Beach': {
            'Nob Hill': 7,
            "Fisherman's Wharf": 5,
            'Bayview': 22
        },
        "Fisherman's Wharf": {
            'Nob Hill': 11,
            'North Beach': 6,
            'Bayview': 26
        },
        'Bayview': {
            'Nob Hill': 20,
            'North Beach': 21,
            "Fisherman's Wharf": 25
        }
    }

    start_time = 540  # 9:00 AM
    start_location = 'Nob Hill'

    best_itinerary = []
    best_length = 0

    for perm in itertools.permutations(friends):
        current_time = start_time
        current_location = start_location
        itinerary = []

        for friend in perm:
            try:
                travel_time_val = travel_times[current_location][friend['location']]
            except KeyError:
                break
            arrival_time = current_time + travel_time_val

            available_start = friend['available_start']
            available_end = friend['available_end']
            required_duration = friend['required_duration']

            earliest_start = max(arrival_time, available_start)
            latest_start = available_end - required_duration

            if earliest_start > latest_start:
                break

            meeting_start = earliest_start
            meeting_end = meeting_start + required_duration

            itinerary.append({
                'action': 'meet',
                'location': friend['location'],
                'person': friend['name'],
                'start_time': minutes_to_time_str(meeting_start),
                'end_time': minutes_to_time_str(meeting_end)
            })

            current_time = meeting_end
            current_location = friend['location']
        else:
            if len(itinerary) > best_length:
                best_length = len(itinerary)
                best_itinerary = itinerary

    result = {"itinerary": best_itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()