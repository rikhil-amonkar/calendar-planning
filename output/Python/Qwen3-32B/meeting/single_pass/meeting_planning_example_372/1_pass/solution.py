import itertools
import json

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m}"

def is_feasible(sequence, travel_times):
    current_time = time_to_minutes("9:00")
    current_location = "Sunset District"
    for friend in sequence:
        dest = friend['location']
        if current_location not in travel_times or dest not in travel_times[current_location]:
            return False
        travel_time = travel_times[current_location][dest]
        arrival_time = current_time + travel_time
        available_start = time_to_minutes(friend['available_start'])
        available_end = time_to_minutes(friend['available_end'])
        required = friend['required_duration']
        earliest_start = max(arrival_time, available_start)
        latest_start = available_end - required
        if earliest_start > latest_start:
            return False
        current_time = earliest_start + required
        current_location = dest
    return True

def main():
    friends = [
        {
            'name': 'Daniel',
            'location': 'Golden Gate Park',
            'available_start': '8:00',
            'available_end': '13:30',
            'required_duration': 15
        },
        {
            'name': 'Margaret',
            'location': 'Russian Hill',
            'available_start': '9:00',
            'available_end': '16:00',
            'required_duration': 30
        },
        {
            'name': 'Charles',
            'location': 'Alamo Square',
            'available_start': '18:00',
            'available_end': '20:45',
            'required_duration': 90
        },
        {
            'name': 'Stephanie',
            'location': 'Mission District',
            'available_start': '20:30',
            'available_end': '22:00',
            'required_duration': 90
        }
    ]

    travel_times = {
        'Sunset District': {
            'Alamo Square': 17,
            'Russian Hill': 24,
            'Golden Gate Park': 11,
            'Mission District': 24
        },
        'Alamo Square': {
            'Sunset District': 16,
            'Russian Hill': 13,
            'Golden Gate Park': 9,
            'Mission District': 10
        },
        'Russian Hill': {
            'Sunset District': 23,
            'Alamo Square': 15,
            'Golden Gate Park': 21,
            'Mission District': 16
        },
        'Golden Gate Park': {
            'Sunset District': 10,
            'Alamo Square': 10,
            'Russian Hill': 19,
            'Mission District': 17
        },
        'Mission District': {
            'Sunset District': 24,
            'Alamo Square': 11,
            'Russian Hill': 15,
            'Golden Gate Park': 17
        }
    }

    best_sequence = None
    max_length = 0

    for k in range(1, len(friends) + 1):
        for subset in itertools.combinations(friends, k):
            for perm in itertools.permutations(subset):
                if is_feasible(perm, travel_times):
                    if len(perm) > max_length:
                        max_length = len(perm)
                        best_sequence = perm

    if best_sequence is None:
        print(json.dumps({"itinerary": []}))
        return

    current_time = time_to_minutes("9:00")
    current_location = "Sunset District"
    itinerary = []

    for friend in best_sequence:
        dest = friend['location']
        travel_time = travel_times[current_location][dest]
        arrival_time = current_time + travel_time
        available_start = time_to_minutes(friend['available_start'])
        available_end = time_to_minutes(friend['available_end'])
        required = friend['required_duration']
        earliest_start = max(arrival_time, available_start)
        latest_start = available_end - required
        meeting_start = earliest_start
        meeting_end = meeting_start + required
        itinerary.append({
            "action": "meet",
            "location": dest,
            "person": friend['name'],
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        })
        current_time = meeting_end
        current_location = dest

    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()