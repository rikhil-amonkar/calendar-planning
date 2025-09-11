import itertools
import json

def time_to_minutes(t_str):
    h, m = map(int, t_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def main():
    friends = [
        {
            'name': 'Ronald',
            'location': 'Russian Hill',
            'available_start': time_to_minutes('13:45'),
            'available_end': time_to_minutes('17:15'),
            'min_duration': 105,
        },
        {
            'name': 'Patricia',
            'location': 'Sunset District',
            'available_start': time_to_minutes('9:15'),
            'available_end': time_to_minutes('22:00'),
            'min_duration': 60,
        },
        {
            'name': 'Laura',
            'location': 'North Beach',
            'available_start': time_to_minutes('12:30'),
            'available_end': time_to_minutes('12:45'),
            'min_duration': 15,
        },
        {
            'name': 'Emily',
            'location': 'The Castro',
            'available_start': time_to_minutes('16:15'),
            'available_end': time_to_minutes('18:30'),
            'min_duration': 60,
        },
        {
            'name': 'Mary',
            'location': 'Golden Gate Park',
            'available_start': time_to_minutes('15:00'),
            'available_end': time_to_minutes('16:30'),
            'min_duration': 60,
        },
    ]

    travel_times = {
        'Financial District': {
            'Russian Hill': 10,
            'Sunset District': 31,
            'North Beach': 7,
            'The Castro': 23,
            'Golden Gate Park': 23,
        },
        'Russian Hill': {
            'Financial District': 11,
            'Sunset District': 23,
            'North Beach': 5,
            'The Castro': 21,
            'Golden Gate Park': 21,
        },
        'Sunset District': {
            'Financial District': 30,
            'Russian Hill': 24,
            'North Beach': 29,
            'The Castro': 17,
            'Golden Gate Park': 11,
        },
        'North Beach': {
            'Financial District': 8,
            'Russian Hill': 4,
            'Sunset District': 27,
            'The Castro': 22,
            'Golden Gate Park': 22,
        },
        'The Castro': {
            'Financial District': 20,
            'Russian Hill': 18,
            'Sunset District': 17,
            'North Beach': 20,
            'Golden Gate Park': 13,
        },
        'Golden Gate Park': {
            'Financial District': 26,
            'Russian Hill': 19,
            'Sunset District': 10,
            'North Beach': 24,
            'The Castro': 13,
        },
    }

    best_itinerary = None

    for k in range(len(friends), 0, -1):
        for subset in itertools.combinations(friends, k):
            for perm in itertools.permutations(subset):
                current_time = 540  # 9:00 AM
                current_location = 'Financial District'
                itinerary = []
                valid = True
                for friend in perm:
                    next_location = friend['location']
                    if current_location not in travel_times or next_location not in travel_times[current_location]:
                        valid = False
                        break
                    travel_time = travel_times[current_location][next_location]
                    arrival_time = current_time + travel_time

                    friend_start = friend['available_start']
                    friend_end = friend['available_end']
                    required = friend['min_duration']

                    earliest_start = max(arrival_time, friend_start)
                    latest_start = friend_end - required

                    if earliest_start > latest_start:
                        valid = False
                        break

                    meeting_start = earliest_start
                    meeting_end = meeting_start + required

                    itinerary.append({
                        'action': 'meet',
                        'location': next_location,
                        'person': friend['name'],
                        'start_time': minutes_to_time(meeting_start),
                        'end_time': minutes_to_time(meeting_end),
                    })

                    current_time = meeting_end
                    current_location = next_location

                if valid:
                    best_itinerary = itinerary
                    print(json.dumps({"itinerary": best_itinerary}))
                    return

    print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()