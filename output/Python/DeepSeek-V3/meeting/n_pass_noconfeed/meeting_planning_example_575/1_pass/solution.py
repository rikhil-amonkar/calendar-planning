import json
from itertools import permutations

def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Define travel times (in minutes) between locations
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
        'Mission District': 11,
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

# Define friend constraints
friends = [
    {
        'name': 'Rebecca',
        'location': 'Presidio',
        'available_start': '18:15',
        'available_end': '20:45',
        'min_duration': 60
    },
    {
        'name': 'Linda',
        'location': 'Sunset District',
        'available_start': '15:30',
        'available_end': '19:45',
        'min_duration': 30
    },
    {
        'name': 'Elizabeth',
        'location': 'Haight-Ashbury',
        'available_start': '17:15',
        'available_end': '19:30',
        'min_duration': 105
    },
    {
        'name': 'William',
        'location': 'Mission District',
        'available_start': '13:15',
        'available_end': '19:30',
        'min_duration': 30
    },
    {
        'name': 'Robert',
        'location': 'Golden Gate Park',
        'available_start': '14:15',
        'available_end': '21:30',
        'min_duration': 45
    },
    {
        'name': 'Mark',
        'location': 'Russian Hill',
        'available_start': '10:00',
        'available_end': '21:15',
        'min_duration': 75
    }
]

def calculate_schedule():
    best_schedule = []
    max_meetings = 0
    
    # Generate all possible permutations of friends
    for perm in permutations(friends):
        current_location = 'The Castro'
        current_time = time_to_minutes('9:00')
        schedule = []
        meetings = 0
        
        for friend in perm:
            travel_time = travel_times[current_location][friend['location']]
            arrival_time = current_time + travel_time
            available_start = time_to_minutes(friend['available_start'])
            available_end = time_to_minutes(friend['available_end'])
            
            # Calculate possible meeting window
            meeting_start = max(arrival_time, available_start)
            meeting_end = min(meeting_start + friend['min_duration'], available_end)
            
            if meeting_end - meeting_start >= friend['min_duration']:
                schedule.append({
                    'action': 'meet',
                    'location': friend['location'],
                    'person': friend['name'],
                    'start_time': minutes_to_time(meeting_start),
                    'end_time': minutes_to_time(meeting_end)
                })
                current_time = meeting_end
                current_location = friend['location']
                meetings += 1
            else:
                # Skip this friend if we can't meet the minimum duration
                continue
        
        if meetings > max_meetings or (meetings == max_meetings and len(schedule) > len(best_schedule)):
            max_meetings = meetings
            best_schedule = schedule
    
    return best_schedule

def main():
    schedule = calculate_schedule()
    result = {
        "itinerary": schedule
    }
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()