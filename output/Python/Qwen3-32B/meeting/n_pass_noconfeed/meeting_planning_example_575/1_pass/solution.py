import itertools
import json

def main():
    friends = [
        {
            'name': 'Rebecca',
            'location': 'Presidio',
            'start_time': 18 * 60 + 15,  # 1095
            'end_time': 20 * 60 + 45,    # 1245
            'duration': 60
        },
        {
            'name': 'Linda',
            'location': 'Sunset District',
            'start_time': 15 * 60 + 30,  # 930
            'end_time': 19 * 60 + 45,    # 1185
            'duration': 30
        },
        {
            'name': 'Elizabeth',
            'location': 'Haight-Ashbury',
            'start_time': 17 * 60 + 15,  # 1035
            'end_time': 19 * 60 + 30,    # 1170
            'duration': 105
        },
        {
            'name': 'William',
            'location': 'Mission District',
            'start_time': 13 * 60 + 15,  # 795
            'end_time': 19 * 60 + 30,    # 1170
            'duration': 30
        },
        {
            'name': 'Robert',
            'location': 'Golden Gate Park',
            'start_time': 14 * 60 + 15,  # 855
            'end_time': 21 * 60 + 30,    # 1290
            'duration': 45
        },
        {
            'name': 'Mark',
            'location': 'Russian Hill',
            'start_time': 10 * 60 + 0,   # 600
            'end_time': 21 * 60 + 15,    # 1275
            'duration': 75
        }
    ]

    travel_times = {
        'The Castro': {
            'Presidio': 20,
            'Sunset District': 17,
            'Haight-Ashbury': 6,
            'Mission District': 7,
            'Golden Gate Park': 11,
            'Russian Hill': 18
        },
        'Presidio': {
            'The Castro': 21,
            'Sunset District': 15,
            'Haight-Ashbury': 15,
            'Mission District': 26,
            'Golden Gate Park': 12,
            'Russian Hill': 14
        },
        'Sunset District': {
            'The Castro': 17,
            'Presidio': 16,
            'Haight-Ashbury': 15,
            'Mission District': 24,
            'Golden Gate Park': 11,
            'Russian Hill': 24
        },
        'Haight-Ashbury': {
            'The Castro': 6,
            'Presidio': 15,
            'Sunset District': 15,
            'Mission District': 12,
            'Golden Gate Park': 7,
            'Russian Hill': 17
        },
        'Mission District': {
            'The Castro': 7,
            'Presidio': 25,
            'Sunset District': 24,
            'Haight-Ashbury': 12,
            'Golden Gate Park': 17,
            'Russian Hill': 15
        },
        'Golden Gate Park': {
            'The Castro': 13,
            'Presidio': 11,
            'Sunset District': 10,
            'Haight-Ashbury': 7,
            'Mission District': 17,
            'Russian Hill': 19
        },
        'Russian Hill': {
            'The Castro': 21,
            'Presidio': 14,
            'Sunset District': 23,
            'Haight-Ashbury': 17,
            'Mission District': 16,
            'Golden Gate Park': 21
        }
    }

    def is_valid_permutation(perm):
        current_time = 540  # 9:00 AM in minutes
        previous_location = 'The Castro'
        for friend in perm:
            travel_time = travel_times[previous_location][friend['location']]
            arrival_time = current_time + travel_time
            earliest_start = max(arrival_time, friend['start_time'])
            if earliest_start + friend['duration'] > friend['end_time']:
                return False
            current_time = earliest_start + friend['duration']
            previous_location = friend['location']
        return True

    def build_itinerary(perm):
        itinerary = []
        current_time = 540
        previous_location = 'The Castro'
        for friend in perm:
            travel_time = travel_times[previous_location][friend['location']]
            arrival_time = current_time + travel_time
            earliest_start = max(arrival_time, friend['start_time'])
            end_time_meeting = earliest_start + friend['duration']
            itinerary.append({
                "action": "meet",
                "location": friend['location'],
                "person": friend['name'],
                "start_time": format_time(earliest_start),
                "end_time": format_time(end_time_meeting)
            })
            current_time = end_time_meeting
            previous_location = friend['location']
        return {"itinerary": itinerary}

    def format_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours}:{mins:02d}"

    def find_optimal_schedule():
        for r in range(len(friends), 0, -1):
            for subset in itertools.combinations(friends, r):
                for perm in itertools.permutations(subset):
                    if is_valid_permutation(perm):
                        return build_itinerary(perm)
        return {"itinerary": []}

    schedule = find_optimal_schedule()
    print(json.dumps(schedule, indent=2))

if __name__ == "__main__":
    main()