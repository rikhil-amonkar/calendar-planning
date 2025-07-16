import json
from itertools import permutations

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Input data with complete travel times
travel_times = {
    'Presidio': {
        'Presidio': 0,
        'Haight-Ashbury': 15,
        'Nob Hill': 18,
        'Russian Hill': 14,
        'North Beach': 18,
        'Chinatown': 21,
        'Union Square': 22,
        'Embarcadero': 20,
        'Financial District': 23,
        'Marina District': 11
    },
    'Haight-Ashbury': {
        'Presidio': 15,
        'Haight-Ashbury': 0,
        'Nob Hill': 15,
        'Russian Hill': 17,
        'North Beach': 19,
        'Chinatown': 19,
        'Union Square': 19,
        'Embarcadero': 20,
        'Financial District': 21,
        'Marina District': 17
    },
    'Nob Hill': {
        'Presidio': 17,
        'Haight-Ashbury': 13,
        'Nob Hill': 0,
        'Russian Hill': 5,
        'North Beach': 8,
        'Chinatown': 6,
        'Union Square': 7,
        'Embarcadero': 9,
        'Financial District': 9,
        'Marina District': 11
    },
    'Russian Hill': {
        'Presidio': 14,
        'Haight-Ashbury': 17,
        'Nob Hill': 5,
        'Russian Hill': 0,
        'North Beach': 5,
        'Chinatown': 9,
        'Union Square': 10,
        'Embarcadero': 8,
        'Financial District': 11,
        'Marina District': 7
    },
    'North Beach': {
        'Presidio': 17,
        'Haight-Ashbury': 18,
        'Nob Hill': 7,
        'Russian Hill': 4,
        'North Beach': 0,
        'Chinatown': 6,
        'Union Square': 7,
        'Embarcadero': 6,
        'Financial District': 8,
        'Marina District': 9
    },
    'Chinatown': {
        'Presidio': 19,
        'Haight-Ashbury': 19,
        'Nob Hill': 9,
        'Russian Hill': 7,
        'North Beach': 3,
        'Chinatown': 0,
        'Union Square': 7,
        'Embarcadero': 5,
        'Financial District': 5,
        'Marina District': 12
    },
    'Union Square': {
        'Presidio': 24,
        'Haight-Ashbury': 18,
        'Nob Hill': 9,
        'Russian Hill': 13,
        'North Beach': 10,
        'Chinatown': 7,
        'Union Square': 0,
        'Embarcadero': 11,
        'Financial District': 9,
        'Marina District': 18
    },
    'Embarcadero': {
        'Presidio': 20,
        'Haight-Ashbury': 21,
        'Nob Hill': 10,
        'Russian Hill': 8,
        'North Beach': 5,
        'Chinatown': 7,
        'Union Square': 10,
        'Embarcadero': 0,
        'Financial District': 5,
        'Marina District': 12
    },
    'Financial District': {
        'Presidio': 22,
        'Haight-Ashbury': 19,
        'Nob Hill': 8,
        'Russian Hill': 11,
        'North Beach': 7,
        'Chinatown': 5,
        'Union Square': 9,
        'Embarcadero': 4,
        'Financial District': 0,
        'Marina District': 15
    },
    'Marina District': {
        'Presidio': 10,
        'Haight-Ashbury': 16,
        'Nob Hill': 12,
        'Russian Hill': 8,
        'North Beach': 11,
        'Chinatown': 15,
        'Union Square': 16,
        'Embarcadero': 14,
        'Financial District': 17,
        'Marina District': 0
    }
}

friends = [
    {
        'name': 'Karen',
        'location': 'Haight-Ashbury',
        'available_start': '21:00',
        'available_end': '21:45',
        'duration': 45
    },
    {
        'name': 'Jessica',
        'location': 'Nob Hill',
        'available_start': '13:45',
        'available_end': '21:00',
        'duration': 90
    },
    {
        'name': 'Brian',
        'location': 'Russian Hill',
        'available_start': '15:30',
        'available_end': '21:45',
        'duration': 60
    },
    {
        'name': 'Kenneth',
        'location': 'North Beach',
        'available_start': '9:45',
        'available_end': '21:00',
        'duration': 30
    },
    {
        'name': 'Jason',
        'location': 'Chinatown',
        'available_start': '8:15',
        'available_end': '11:45',
        'duration': 75
    },
    {
        'name': 'Stephanie',
        'location': 'Union Square',
        'available_start': '14:45',
        'available_end': '18:45',
        'duration': 105
    },
    {
        'name': 'Kimberly',
        'location': 'Embarcadero',
        'available_start': '9:45',
        'available_end': '19:30',
        'duration': 75
    },
    {
        'name': 'Steven',
        'location': 'Financial District',
        'available_start': '7:15',
        'available_end': '21:15',
        'duration': 60
    },
    {
        'name': 'Mark',
        'location': 'Marina District',
        'available_start': '10:15',
        'available_end': '13:00',
        'duration': 75
    }
]

def get_travel_time(from_loc, to_loc):
    return travel_times[from_loc][to_loc]

def is_meeting_possible(schedule, friend, current_time, current_location):
    available_start = time_to_minutes(friend['available_start'])
    available_end = time_to_minutes(friend['available_end'])
    duration = friend['duration']
    
    travel_time = get_travel_time(current_location, friend['location'])
    arrival_time = current_time + travel_time
    
    if arrival_time > available_end:
        return False
    
    start_time = max(arrival_time, available_start)
    end_time = start_time + duration
    
    if end_time > available_end:
        return False
    
    # Check if this overlaps with any existing meeting
    for meeting in schedule:
        meeting_start = time_to_minutes(meeting['start_time'])
        meeting_end = time_to_minutes(meeting['end_time'])
        if not (end_time <= meeting_start or start_time >= meeting_end):
            return False
    
    return True

def add_meeting(schedule, friend, current_time, current_location):
    available_start = time_to_minutes(friend['available_start'])
    duration = friend['duration']
    
    travel_time = get_travel_time(current_location, friend['location'])
    arrival_time = current_time + travel_time
    start_time = max(arrival_time, available_start)
    end_time = start_time + duration
    
    meeting = {
        'action': 'meet',
        'location': friend['location'],
        'person': friend['name'],
        'start_time': minutes_to_time(start_time),
        'end_time': minutes_to_time(end_time)
    }
    
    schedule.append(meeting)
    return end_time, friend['location']

def evaluate_schedule(order):
    schedule = []
    current_time = time_to_minutes('9:00')
    current_location = 'Presidio'
    
    for friend_idx in order:
        friend = friends[friend_idx]
        if is_meeting_possible(schedule, friend, current_time, current_location):
            current_time, current_location = add_meeting(schedule, friend, current_time, current_location)
    
    return schedule

def main():
    best_schedule = []
    best_count = 0
    
    # We'll try all possible orders of friends to find the best schedule
    # Since there are 9 friends, we'll limit permutations to avoid excessive computation
    for order in permutations(range(len(friends)), min(5, len(friends))):
        schedule = evaluate_schedule(order)
        if len(schedule) > best_count:
            best_count = len(schedule)
            best_schedule = schedule
    
    # Try to add Karen at the end if possible (she's only available late)
    karen = next(f for f in friends if f['name'] == 'Karen')
    current_time = time_to_minutes('9:00')
    current_location = 'Presidio'
    
    if best_schedule:
        current_time = time_to_minutes(best_schedule[-1]['end_time'])
        current_location = best_schedule[-1]['location']
    
    if is_meeting_possible(best_schedule, karen, current_time, current_location):
        add_meeting(best_schedule, karen, current_time, current_location)
    
    # Output the result
    result = {
        "itinerary": best_schedule
    }
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()