import itertools
import json

def minutes_to_time_str(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

def find_optimal_schedule():
    travel_times = {
        'Bayview': {
            'Embarcadero': 19,
            "Fisherman's Wharf": 25,
            'Financial District': 19
        },
        'Embarcadero': {
            'Bayview': 21,
            "Fisherman's Wharf": 6,
            'Financial District': 5
        },
        "Fisherman's Wharf": {
            'Bayview': 26,
            'Embarcadero': 8,
            'Financial District': 11
        },
        'Financial District': {
            'Bayview': 19,
            'Embarcadero': 4,
            "Fisherman's Wharf": 10
        }
    }

    friends = [
        {
            'name': 'Karen',
            'location': "Fisherman's Wharf",
            'start_time': 8 * 60 + 45,  # 525
            'end_time': 15 * 60,        # 900
            'required': 30
        },
        {
            'name': 'Anthony',
            'location': 'Financial District',
            'start_time': 9 * 60 + 15,  # 555
            'end_time': 21 * 60 + 30,   # 1290
            'required': 105
        },
        {
            'name': 'Betty',
            'location': 'Embarcadero',
            'start_time': 19 * 60 + 45, # 1185
            'end_time': 21 * 60 + 45,   # 1245
            'required': 15
        }
    ]

    start_location = 'Bayview'
    start_time_minutes = 9 * 60  # 9:00 AM

    best_itinerary = []
    max_meetings = 0

    for perm in itertools.permutations(friends):
        current_location = start_location
        current_time = start_time_minutes
        itinerary = []
        valid = True

        for friend in perm:
            # Compute travel time
            dest = friend['location']
            if current_location not in travel_times or dest not in travel_times[current_location]:
                valid = False
                break
            travel_duration = travel_times[current_location][dest]
            arrival_time = current_time + travel_duration

            # Friend's availability
            friend_start = friend['start_time']
            friend_end = friend['end_time']
            required = friend['required']

            # The earliest we can start meeting is max(arrival_time, friend's start)
            meeting_start = max(arrival_time, friend_start)
            meeting_end = meeting_start + required

            # Check if meeting_end exceeds friend's end time
            if meeting_end > friend_end:
                valid = False
                break

            # Add to itinerary
            itinerary.append({
                'action': 'meet',
                'location': dest,
                'person': friend['name'],
                'start_time': minutes_to_time_str(meeting_start),
                'end_time': minutes_to_time_str(meeting_end)
            })

            # Update current time and location
            current_time = meeting_end
            current_location = dest

        if valid and len(itinerary) > max_meetings:
            max_meetings = len(itinerary)
            best_itinerary = itinerary

    return best_itinerary

itinerary = find_optimal_schedule()
result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))