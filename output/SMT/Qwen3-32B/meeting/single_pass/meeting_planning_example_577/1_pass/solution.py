import itertools
import json

def time_to_minutes(t):
    h, m = map(int, t.split(':'))
    return h * 60 + m

def is_feasible(perm, travel_times):
    current_time = 9 * 60  # 9:00 AM
    current_location = 'Haight-Ashbury'

    for friend in perm:
        location = friend['location']
        travel_time = travel_times[current_location][location]
        arrival_time = current_time + travel_time

        available_start = time_to_minutes(friend['available'][0])
        available_end = time_to_minutes(friend['available'][1])
        duration = friend['duration']

        earliest_start = max(arrival_time, available_start)
        latest_start = available_end - duration

        if earliest_start > latest_start:
            return False

        current_time = earliest_start + duration
        current_location = location

    return True

def generate_itinerary(perm, travel_times):
    current_time = 9 * 60
    current_location = 'Haight-Ashbury'
    itinerary = []

    for friend in perm:
        location = friend['location']
        travel_time = travel_times[current_location][location]
        arrival_time = current_time + travel_time

        available_start = time_to_minutes(friend['available'][0])
        available_end = time_to_minutes(friend['available'][1])
        duration = friend['duration']

        earliest_start = max(arrival_time, available_start)
        latest_start = available_end - duration

        start_time_minutes = earliest_start
        end_time_minutes = start_time_minutes + duration

        start_time = f"{start_time_minutes // 60:02d}:{start_time_minutes % 60:02d}"
        end_time = f"{end_time_minutes // 60:02d}:{end_time_minutes % 60:02d}"

        itinerary.append({
            "action": "meet",
            "person": friend['name'],
            "start_time": start_time,
            "end_time": end_time,
        })

        current_time = end_time_minutes
        current_location = location

    return itinerary

def main():
    friends = [
        {
            'name': 'Anthony',
            'location': 'Alamo Square',
            'available': ('07:45', '19:45'),
            'duration': 15,
        },
        {
            'name': 'Steven',
            'location': 'Golden Gate Park',
            'available': ('08:30', '17:00'),
            'duration': 75,
        },
        {
            'name': 'Sandra',
            'location': 'Pacific Heights',
            'available': ('14:45', '21:45'),
            'duration': 45,
        },
        {
            'name': 'Kevin',
            'location': 'Fisherman\'s Wharf',
            'available': ('19:15', '21:45'),
            'duration': 75,
        },
        {
            'name': 'Stephanie',
            'location': 'Russian Hill',
            'available': ('20:00', '20:45'),
            'duration': 15,
        },
    ]

    travel_times = {
        'Haight-Ashbury': {
            'Russian Hill': 17,
            'Fisherman\'s Wharf': 23,
            'Nob Hill': 15,
            'Golden Gate Park': 7,
            'Alamo Square': 5,
            'Pacific Heights': 12,
        },
        'Russian Hill': {
            'Haight-Ashbury': 17,
            'Fisherman\'s Wharf': 7,
            'Nob Hill': 5,
            'Golden Gate Park': 21,
            'Alamo Square': 15,
            'Pacific Heights': 7,
        },
        'Fisherman\'s Wharf': {
            'Haight-Ashbury': 22,
            'Russian Hill': 7,
            'Nob Hill': 11,
            'Golden Gate Park': 25,
            'Alamo Square': 20,
            'Pacific Heights': 12,
        },
        'Nob Hill': {
            'Haight-Ashbury': 13,
            'Russian Hill': 5,
            'Fisherman\'s Wharf': 11,
            'Golden Gate Park': 17,
            'Alamo Square': 11,
            'Pacific Heights': 8,
        },
        'Golden Gate Park': {
            'Haight-Ashbury': 7,
            'Russian Hill': 19,
            'Fisherman\'s Wharf': 24,
            'Nob Hill': 17,
            'Alamo Square': 10,
            'Pacific Heights': 16,
        },
        'Alamo Square': {
            'Haight-Ashbury': 5,
            'Russian Hill': 13,
            'Fisherman\'s Wharf': 19,
            'Nob Hill': 11,
            'Golden Gate Park': 9,
            'Pacific Heights': 10,
        },
        'Pacific Heights': {
            'Haight-Ashbury': 11,
            'Russian Hill': 7,
            'Fisherman\'s Wharf': 13,
            'Nob Hill': 8,
            'Golden Gate Park': 15,
            'Alamo Square': 10,
        },
    }

    for k in range(len(friends), 0, -1):
        for subset in itertools.combinations(friends, k):
            for perm in itertools.permutations(subset):
                if is_feasible(perm, travel_times):
                    itinerary = generate_itinerary(perm, travel_times)
                    print(json.dumps({"itinerary": itinerary}))
                    return

if __name__ == "__main__":
    main()