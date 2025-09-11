import itertools
import json

def minutes_to_time_str(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

# Define travel times between locations
travel_times = {
    'Embarcadero': {
        'Golden Gate Park': 25,
        'Haight-Ashbury': 21,
        'Bayview': 21,
        'Presidio': 20,
        'Financial District': 5
    },
    'Golden Gate Park': {
        'Embarcadero': 25,
        'Haight-Ashbury': 7,
        'Bayview': 23,
        'Presidio': 11,
        'Financial District': 26
    },
    'Haight-Ashbury': {
        'Embarcadero': 20,
        'Golden Gate Park': 7,
        'Bayview': 18,
        'Presidio': 15,
        'Financial District': 21
    },
    'Bayview': {
        'Embarcadero': 19,
        'Golden Gate Park': 22,
        'Haight-Ashbury': 19,
        'Presidio': 31,
        'Financial District': 19
    },
    'Presidio': {
        'Embarcadero': 20,
        'Golden Gate Park': 12,
        'Haight-Ashbury': 15,
        'Bayview': 31,
        'Financial District': 23
    },
    'Financial District': {
        'Embarcadero': 4,
        'Golden Gate Park': 23,
        'Haight-Ashbury': 19,
        'Bayview': 19,
        'Presidio': 22
    }
}

# Define friend availability and meeting requirements
friends = [
    {
        'name': 'Mary',
        'location': 'Golden Gate Park',
        'earliest': 8 * 60 + 45,  # 8:45 AM
        'latest': 11 * 60 + 45,   # 11:45 AM
        'duration': 45
    },
    {
        'name': 'Kevin',
        'location': 'Haight-Ashbury',
        'earliest': 10 * 60 + 15,  # 10:15 AM
        'latest': 16 * 60 + 15,    # 4:15 PM
        'duration': 90
    },
    {
        'name': 'Deborah',
        'location': 'Bayview',
        'earliest': 15 * 60 + 0,   # 3:00 PM
        'latest': 19 * 60 + 15,    # 7:15 PM
        'duration': 120
    },
    {
        'name': 'Stephanie',
        'location': 'Presidio',
        'earliest': 10 * 60 + 0,   # 10:00 AM
        'latest': 17 * 60 + 15,    # 5:15 PM
        'duration': 120
    },
    {
        'name': 'Emily',
        'location': 'Financial District',
        'earliest': 11 * 60 + 30,  # 11:30 AM
        'latest': 21 * 60 + 45,    # 9:45 PM
        'duration': 105
    }
]

best_meetings = []
best_count = 0

# Try all possible permutations of friends to find the optimal schedule
for r in range(len(friends), 0, -1):
    for subset in itertools.combinations(friends, r):
        for perm in itertools.permutations(subset):
            current_time = 9 * 60  # Start at 9:00 AM
            current_location = 'Embarcadero'
            valid = True
            meetings = []
            
            for friend in perm:
                dest = friend['location']
                if current_location not in travel_times or dest not in travel_times[current_location]:
                    valid = False
                    break
                
                travel_time = travel_times[current_location][dest]
                arrival_time = current_time + travel_time
                earliest_start = max(arrival_time, friend['earliest'])
                
                if earliest_start + friend['duration'] <= friend['latest']:
                    end_time = earliest_start + friend['duration']
                    meetings.append((friend, earliest_start, end_time))
                    current_time = end_time
                    current_location = dest
                else:
                    valid = False
                    break
            
            if valid:
                if len(meetings) > best_count:
                    best_count = len(meetings)
                    best_meetings = meetings
                elif len(meetings) == best_count and best_count > 0:
                    # Tie-breaker: choose the one with earliest first meeting
                    if best_meetings and meetings:
                        if meetings[0][1] < best_meetings[0][1]:
                            best_meetings = meetings
    if best_count >= r:
        break

# Generate the JSON output
itinerary = []
for meeting in best_meetings:
    friend, start, end = meeting
    itinerary.append({
        "action": "meet",
        "location": friend['location'],
        "person": friend['name'],
        "start_time": minutes_to_time_str(start),
        "end_time": minutes_to_time_str(end)
    })

print(json.dumps({"itinerary": itinerary}, indent=2))