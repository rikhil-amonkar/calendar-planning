import json
from itertools import permutations

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Locations
LOCATIONS = ['Nob Hill', 'North Beach', 'Fisherman\'s Wharf', 'Bayview']

# Travel times in minutes (from -> to)
TRAVEL_TIMES = {
    'Nob Hill': {'North Beach': 8, 'Fisherman\'s Wharf': 11, 'Bayview': 19},
    'North Beach': {'Nob Hill': 7, 'Fisherman\'s Wharf': 5, 'Bayview': 22},
    'Fisherman\'s Wharf': {'Nob Hill': 11, 'North Beach': 6, 'Bayview': 26},
    'Bayview': {'Nob Hill': 20, 'North Beach': 21, 'Fisherman\'s Wharf': 25}
}

# Constraints
START_LOCATION = 'Nob Hill'
START_TIME = '9:00'

FRIENDS = [
    {
        'name': 'Helen',
        'location': 'North Beach',
        'available_start': '7:00',
        'available_end': '16:45',
        'min_duration': 120
    },
    {
        'name': 'Kimberly',
        'location': 'Fisherman\'s Wharf',
        'available_start': '16:30',
        'available_end': '21:00',
        'min_duration': 45
    },
    {
        'name': 'Patricia',
        'location': 'Bayview',
        'available_start': '18:00',
        'available_end': '21:15',
        'min_duration': 120
    }
]

def calculate_schedule():
    best_schedule = None
    max_meetings = 0
    
    # Generate all possible meeting orders
    for order in permutations(FRIENDS):
        current_location = START_LOCATION
        current_time = time_to_minutes(START_TIME)
        schedule = []
        valid = True
        
        for friend in order:
            # Calculate travel time to friend's location
            travel_time = TRAVEL_TIMES[current_location][friend['location']]
            arrival_time = current_time + travel_time
            
            # Check if we can meet the friend
            available_start = time_to_minutes(friend['available_start'])
            available_end = time_to_minutes(friend['available_end'])
            
            # Determine meeting start and end times
            meeting_start = max(arrival_time, available_start)
            meeting_end = meeting_start + friend['min_duration']
            
            if meeting_end > available_end:
                valid = False
                break
            
            # Add to schedule
            schedule.append({
                'action': 'meet',
                'location': friend['location'],
                'person': friend['name'],
                'start_time': minutes_to_time(meeting_start),
                'end_time': minutes_to_time(meeting_end)
            })
            
            # Update current time and location
            current_time = meeting_end
            current_location = friend['location']
        
        if valid and len(schedule) >= max_meetings:
            if len(schedule) > max_meetings or (best_schedule is None or len(schedule) == max_meetings):
                best_schedule = schedule
                max_meetings = len(schedule)
    
    return best_schedule

def main():
    schedule = calculate_schedule()
    result = {
        "itinerary": schedule if schedule else []
    }
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()