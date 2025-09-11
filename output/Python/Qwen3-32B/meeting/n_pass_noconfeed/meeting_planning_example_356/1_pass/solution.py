import itertools
import json

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Define friends with their constraints
friends = [
    {
        'name': 'Barbara',
        'location': 'North Beach',
        'available_start': 13 * 60 + 45,  # 1:45 PM
        'available_end': 20 * 60 + 15,    # 8:15 PM
        'required_duration': 60
    },
    {
        'name': 'Margaret',
        'location': 'Presidio',
        'available_start': 10 * 60 + 15,  # 10:15 AM
        'available_end': 15 * 60 + 15,    # 3:15 PM
        'required_duration': 30
    },
    {
        'name': 'Kimberly',
        'location': 'Union Square',
        'available_start': 7 * 60 + 45,   # 7:45 AM
        'available_end': 16 * 60 + 45,    # 4:45 PM
        'required_duration': 30
    },
    {
        'name': 'Kevin',
        'location': 'Haight-Ashbury',
        'available_start': 20 * 60 + 0,   # 8:00 PM
        'available_end': 20 * 60 + 45,    # 8:45 PM
        'required_duration': 30
    }
]

# Define travel times between locations (in minutes)
travel_times = {
    'Bayview': {
        'North Beach': 21,
        'Presidio': 31,
        'Haight-Ashbury': 19,
        'Union Square': 17
    },
    'North Beach': {
        'Bayview': 22,
        'Presidio': 17,
        'Haight-Ashbury': 18,
        'Union Square': 7
    },
    'Presidio': {
        'Bayview': 31,
        'North Beach': 18,
        'Haight-Ashbury': 15,
        'Union Square': 22
    },
    'Haight-Ashbury': {
        'Bayview': 18,
        'North Beach': 19,
        'Presidio': 15,
        'Union Square': 17
    },
    'Union Square': {
        'Bayview': 15,
        'North Beach': 10,
        'Presidio': 24,
        'Haight-Ashbury': 18
    }
}

# Starting point
start_time_minutes = 9 * 60  # 9:00 AM
start_location = 'Bayview'

best_meetings = []
max_met = 0

# Check all permutations of friends
for r in range(1, 5):  # lengths 1 to 4
    for perm in itertools.permutations(friends, r):
        current_time = start_time_minutes
        current_location = start_location
        valid = True
        meetings = []
        
        for friend in perm:
            # Calculate travel time
            try:
                travel_time = travel_times[current_location][friend['location']]
            except KeyError:
                # if there's no direct travel time (unlikely given input)
                valid = False
                break
            current_time += travel_time
            
            # Check if meeting is possible
            earliest_start = max(current_time, friend['available_start'])
            required_end = earliest_start + friend['required_duration']
            
            if required_end > friend['available_end']:
                valid = False
                break
            
            # Update for next step
            meetings.append({
                'friend': friend,
                'start': earliest_start,
                'end': required_end
            })
            current_time = required_end
            current_location = friend['location']
        
        if valid:
            if len(meetings) > max_met:
                max_met = len(meetings)
                best_meetings = meetings
            elif len(meetings) == max_met and max_met > 0:
                # Compare with current best_meetings
                # For tie-breaker, compare the start time of the first meeting
                # If this permutation's first meeting starts earlier, replace
                if best_meetings:
                    current_first_start = best_meetings[0]['start']
                    new_first_start = meetings[0]['start']
                    if new_first_start < current_first_start:
                        best_meetings = meetings
                else:
                    best_meetings = meetings

# Generate the JSON output
itinerary = []
for meeting in best_meetings:
    friend = meeting['friend']
    start_time = minutes_to_time(meeting['start'])
    end_time = minutes_to_time(meeting['end'])
    itinerary.append({
        "action": "meet",
        "location": friend['location'],
        "person": friend['name'],
        "start_time": start_time,
        "end_time": end_time
    })

result = {"itinerary": itinerary}

print(json.dumps(result, indent=2))