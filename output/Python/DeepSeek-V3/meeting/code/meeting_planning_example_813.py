import json
from itertools import permutations

# Travel times dictionary (from -> to -> minutes)
travel_times = {
    'Marina District': {
        'Embarcadero': 14,
        'Bayview': 27,
        'Union Square': 16,
        'Chinatown': 15,
        'Sunset District': 19,
        'Golden Gate Park': 18,
        'Financial District': 17,
        'Haight-Ashbury': 16,
        'Mission District': 20
    },
    'Embarcadero': {
        'Marina District': 12,
        'Bayview': 21,
        'Union Square': 10,
        'Chinatown': 7,
        'Sunset District': 30,
        'Golden Gate Park': 25,
        'Financial District': 5,
        'Haight-Ashbury': 21,
        'Mission District': 20
    },
    'Bayview': {
        'Marina District': 27,
        'Embarcadero': 19,
        'Union Square': 18,
        'Chinatown': 19,
        'Sunset District': 23,
        'Golden Gate Park': 22,
        'Financial District': 19,
        'Haight-Ashbury': 19,
        'Mission District': 13
    },
    'Union Square': {
        'Marina District': 18,
        'Embarcadero': 11,
        'Bayview': 15,
        'Chinatown': 7,
        'Sunset District': 27,
        'Golden Gate Park': 22,
        'Financial District': 9,
        'Haight-Ashbury': 18,
        'Mission District': 14
    },
    'Chinatown': {
        'Marina District': 12,
        'Embarcadero': 5,
        'Bayview': 20,
        'Union Square': 7,
        'Sunset District': 29,
        'Golden Gate Park': 23,
        'Financial District': 5,
        'Haight-Ashbury': 19,
        'Mission District': 17
    },
    'Sunset District': {
        'Marina District': 21,
        'Embarcadero': 30,
        'Bayview': 22,
        'Union Square': 30,
        'Chinatown': 30,
        'Golden Gate Park': 11,
        'Financial District': 30,
        'Haight-Ashbury': 15,
        'Mission District': 25
    },
    'Golden Gate Park': {
        'Marina District': 16,
        'Embarcadero': 25,
        'Bayview': 23,
        'Union Square': 22,
        'Chinatown': 23,
        'Sunset District': 10,
        'Financial District': 26,
        'Haight-Ashbury': 7,
        'Mission District': 17
    },
    'Financial District': {
        'Marina District': 15,
        'Embarcadero': 4,
        'Bayview': 19,
        'Union Square': 9,
        'Chinatown': 5,
        'Sunset District': 30,
        'Golden Gate Park': 23,
        'Haight-Ashbury': 19,
        'Mission District': 17
    },
    'Haight-Ashbury': {
        'Marina District': 17,
        'Embarcadero': 20,
        'Bayview': 18,
        'Union Square': 19,
        'Chinatown': 19,
        'Sunset District': 15,
        'Golden Gate Park': 7,
        'Financial District': 21,
        'Mission District': 11
    },
    'Mission District': {
        'Marina District': 19,
        'Embarcadero': 19,
        'Bayview': 14,
        'Union Square': 15,
        'Chinatown': 16,
        'Sunset District': 24,
        'Golden Gate Park': 17,
        'Financial District': 15,
        'Haight-Ashbury': 12
    }
}

# Friend constraints
friends = [
    {'name': 'Joshua', 'location': 'Embarcadero', 'start': '9:45', 'end': '18:00', 'duration': 105},
    {'name': 'Jeffrey', 'location': 'Bayview', 'start': '9:45', 'end': '20:15', 'duration': 75},
    {'name': 'Charles', 'location': 'Union Square', 'start': '10:45', 'end': '20:15', 'duration': 120},
    {'name': 'Joseph', 'location': 'Chinatown', 'start': '7:00', 'end': '15:30', 'duration': 60},
    {'name': 'Elizabeth', 'location': 'Sunset District', 'start': '9:00', 'end': '9:45', 'duration': 45},
    {'name': 'Matthew', 'location': 'Golden Gate Park', 'start': '11:00', 'end': '19:30', 'duration': 45},
    {'name': 'Carol', 'location': 'Financial District', 'start': '10:45', 'end': '11:15', 'duration': 15},
    {'name': 'Paul', 'location': 'Haight-Ashbury', 'start': '19:15', 'end': '20:30', 'duration': 15},
    {'name': 'Rebecca', 'location': 'Mission District', 'start': '17:00', 'end': '21:45', 'duration': 45}
]

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def can_schedule(friend, start_time, end_time):
    friend_start = time_to_minutes(friend['start'])
    friend_end = time_to_minutes(friend['end'])
    return start_time >= friend_start and end_time <= friend_end

def find_best_schedule():
    best_schedule = []
    max_meetings = 0
    
    # Try all possible orders of meeting friends (limited to 5 for performance)
    for friend_order in permutations(friends, min(5, len(friends))):
        current_location = 'Marina District'
        current_time = time_to_minutes('9:00')
        schedule = []
        meetings = 0
        
        for friend in friend_order:
            # Calculate travel time
            travel_time = travel_times[current_location][friend['location']]
            arrival_time = current_time + travel_time
            
            # Calculate possible meeting window
            meeting_start = max(arrival_time, time_to_minutes(friend['start']))
            meeting_end = meeting_start + friend['duration']
            
            if can_schedule(friend, meeting_start, meeting_end):
                # Add to schedule
                schedule.append({
                    'action': 'meet',
                    'location': friend['location'],
                    'person': friend['name'],
                    'start_time': minutes_to_time(meeting_start),
                    'end_time': minutes_to_time(meeting_end)
                })
                meetings += 1
                current_location = friend['location']
                current_time = meeting_end
        
        if meetings > max_meetings:
            max_meetings = meetings
            best_schedule = schedule
    
    return best_schedule

def main():
    schedule = find_best_schedule()
    result = {'itinerary': schedule}
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()