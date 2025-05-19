import json
from itertools import permutations

def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    minutes = minutes % 60
    return f"{hours}:{minutes:02d}"

# Travel times dictionary: {from_location: {to_location: minutes}}
travel_times = {
    'Marina District': {
        'Mission District': 20,
        'Fisherman\'s Wharf': 10,
        'Presidio': 10,
        'Union Square': 16,
        'Sunset District': 19,
        'Financial District': 17,
        'Haight-Ashbury': 16,
        'Russian Hill': 8
    },
    'Mission District': {
        'Marina District': 19,
        'Fisherman\'s Wharf': 22,
        'Presidio': 25,
        'Union Square': 15,
        'Sunset District': 24,
        'Financial District': 15,
        'Haight-Ashbury': 12,
        'Russian Hill': 15
    },
    'Fisherman\'s Wharf': {
        'Marina District': 9,
        'Mission District': 22,
        'Presidio': 17,
        'Union Square': 13,
        'Sunset District': 27,
        'Financial District': 11,
        'Haight-Ashbury': 22,
        'Russian Hill': 7
    },
    'Presidio': {
        'Marina District': 11,
        'Mission District': 26,
        'Fisherman\'s Wharf': 19,
        'Union Square': 22,
        'Sunset District': 15,
        'Financial District': 23,
        'Haight-Ashbury': 15,
        'Russian Hill': 14
    },
    'Union Square': {
        'Marina District': 18,
        'Mission District': 14,
        'Fisherman\'s Wharf': 15,
        'Presidio': 24,
        'Sunset District': 27,
        'Financial District': 9,
        'Haight-Ashbury': 18,
        'Russian Hill': 13
    },
    'Sunset District': {
        'Marina District': 21,
        'Mission District': 25,
        'Fisherman\'s Wharf': 29,
        'Presidio': 16,
        'Union Square': 30,
        'Financial District': 30,
        'Haight-Ashbury': 15,
        'Russian Hill': 24
    },
    'Financial District': {
        'Marina District': 15,
        'Mission District': 17,
        'Fisherman\'s Wharf': 10,
        'Presidio': 22,
        'Union Square': 9,
        'Sunset District': 30,
        'Haight-Ashbury': 19,
        'Russian Hill': 11
    },
    'Haight-Ashbury': {
        'Marina District': 17,
        'Mission District': 11,
        'Fisherman\'s Wharf': 23,
        'Presidio': 15,
        'Union Square': 19,
        'Sunset District': 15,
        'Financial District': 21,
        'Russian Hill': 17
    },
    'Russian Hill': {
        'Marina District': 7,
        'Mission District': 16,
        'Fisherman\'s Wharf': 7,
        'Presidio': 14,
        'Union Square': 10,
        'Sunset District': 23,
        'Financial District': 11,
        'Haight-Ashbury': 17
    }
}

# Friend constraints
friends = [
    {'name': 'Karen', 'location': 'Mission District', 'start': '14:15', 'end': '22:00', 'duration': 30},
    {'name': 'Richard', 'location': 'Fisherman\'s Wharf', 'start': '14:30', 'end': '17:30', 'duration': 30},
    {'name': 'Robert', 'location': 'Presidio', 'start': '21:45', 'end': '22:45', 'duration': 60},
    {'name': 'Joseph', 'location': 'Union Square', 'start': '11:45', 'end': '14:45', 'duration': 120},
    {'name': 'Helen', 'location': 'Sunset District', 'start': '14:45', 'end': '20:45', 'duration': 105},
    {'name': 'Elizabeth', 'location': 'Financial District', 'start': '10:00', 'end': '12:45', 'duration': 75},
    {'name': 'Kimberly', 'location': 'Haight-Ashbury', 'start': '14:15', 'end': '17:30', 'duration': 105},
    {'name': 'Ashley', 'location': 'Russian Hill', 'start': '11:30', 'end': '21:30', 'duration': 45}
]

def calculate_schedule():
    best_schedule = None
    max_meetings = 0
    
    # Try different permutations of friends to find the best schedule
    for friend_order in permutations(friends):
        current_location = 'Marina District'
        current_time = time_to_minutes('9:00')
        schedule = []
        meetings = 0
        
        for friend in friend_order:
            # Calculate travel time to friend's location
            travel_time = travel_times[current_location][friend['location']]
            arrival_time = current_time + travel_time
            
            # Check if we can meet this friend
            friend_start = time_to_minutes(friend['start'])
            friend_end = time_to_minutes(friend['end'])
            
            # Calculate possible meeting window
            meeting_start = max(arrival_time, friend_start)
            meeting_end = min(meeting_start + friend['duration'], friend_end)
            
            if meeting_end - meeting_start >= friend['duration']:
                # Can meet this friend
                schedule.append({
                    'action': 'meet',
                    'location': friend['location'],
                    'person': friend['name'],
                    'start_time': minutes_to_time(meeting_start),
                    'end_time': minutes_to_time(meeting_end)
                })
                meetings += 1
                current_time = meeting_end
                current_location = friend['location']
            else:
                # Can't meet this friend, skip
                continue
        
        # Check if this schedule is better than the current best
        if meetings > max_meetings or (meetings == max_meetings and current_time < time_to_minutes('23:59')):
            max_meetings = meetings
            best_schedule = schedule
    
    return best_schedule

def main():
    schedule = calculate_schedule()
    result = {
        'itinerary': schedule
    }
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()