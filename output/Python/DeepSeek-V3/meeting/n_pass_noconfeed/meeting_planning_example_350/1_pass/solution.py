import json
from itertools import permutations

# Travel times in minutes
travel_times = {
    'Bayview': {
        'Pacific Heights': 23,
        'Mission District': 13,
        'Haight-Ashbury': 19,
        'Financial District': 19
    },
    'Pacific Heights': {
        'Bayview': 22,
        'Mission District': 15,
        'Haight-Ashbury': 11,
        'Financial District': 13
    },
    'Mission District': {
        'Bayview': 15,
        'Pacific Heights': 16,
        'Haight-Ashbury': 12,
        'Financial District': 17
    },
    'Haight-Ashbury': {
        'Bayview': 18,
        'Pacific Heights': 12,
        'Mission District': 11,
        'Financial District': 21
    },
    'Financial District': {
        'Bayview': 19,
        'Pacific Heights': 13,
        'Mission District': 17,
        'Haight-Ashbury': 19
    }
}

# Friend constraints
friends = {
    'Mary': {
        'location': 'Pacific Heights',
        'start': 10 * 60,  # 10:00 AM in minutes
        'end': 19 * 60,    # 7:00 PM in minutes
        'duration': 45
    },
    'Lisa': {
        'location': 'Mission District',
        'start': 20 * 60 + 30,  # 8:30 PM in minutes
        'end': 22 * 60,         # 10:00 PM in minutes
        'duration': 75
    },
    'Betty': {
        'location': 'Haight-Ashbury',
        'start': 7 * 60 + 15,  # 7:15 AM in minutes
        'end': 17 * 60 + 15,   # 5:15 PM in minutes
        'duration': 90
    },
    'Charles': {
        'location': 'Financial District',
        'start': 11 * 60 + 15,  # 11:15 AM in minutes
        'end': 15 * 60,         # 3:00 PM in minutes
        'duration': 120
    }
}

def time_to_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def find_best_schedule():
    current_location = 'Bayview'
    current_time = 9 * 60  # 9:00 AM in minutes
    best_schedule = []
    max_meetings = 0

    # Try all permutations of friends to find the best schedule
    for perm in permutations(friends.keys()):
        schedule = []
        temp_location = current_location
        temp_time = current_time
        meetings = 0

        for person in perm:
            friend = friends[person]
            travel_time = travel_times[temp_location][friend['location']]
            arrival_time = temp_time + travel_time

            # Calculate meeting window
            meeting_start = max(arrival_time, friend['start'])
            meeting_end = meeting_start + friend['duration']

            if meeting_end <= friend['end']:
                schedule.append({
                    'action': 'meet',
                    'location': friend['location'],
                    'person': person,
                    'start_time': time_to_str(meeting_start),
                    'end_time': time_to_str(meeting_end)
                })
                meetings += 1
                temp_location = friend['location']
                temp_time = meeting_end
            else:
                break  # Can't meet this friend in this permutation

        if meetings > max_meetings:
            max_meetings = meetings
            best_schedule = schedule

    return best_schedule

def main():
    best_schedule = find_best_schedule()
    result = {
        "itinerary": best_schedule
    }
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()