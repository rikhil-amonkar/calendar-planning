import constraint
from datetime import datetime, timedelta
import json

def time_to_minutes(time_str):
    """Convert time string (H:MM) to minutes since midnight"""
    dt = datetime.strptime(time_str, '%H:%M')
    return dt.hour * 60 + dt.minute

def minutes_to_time(minutes):
    """Convert minutes since midnight to time string (H:MM)"""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    # Travel times in minutes (symmetric matrix)
    travel_times = {
        'Presidio': {
            'Richmond District': 7,
            'North Beach': 18,
            'Financial District': 23,
            'Golden Gate Park': 12,
            'Union Square': 22
        },
        'Richmond District': {
            'Presidio': 7,
            'North Beach': 17,
            'Financial District': 22,
            'Golden Gate Park': 9,
            'Union Square': 21
        },
        'North Beach': {
            'Presidio': 17,
            'Richmond District': 18,
            'Financial District': 8,
            'Golden Gate Park': 22,
            'Union Square': 7
        },
        'Financial District': {
            'Presidio': 22,
            'Richmond District': 21,
            'North Beach': 7,
            'Golden Gate Park': 23,
            'Union Square': 9
        },
        'Golden Gate Park': {
            'Presidio': 11,
            'Richmond District': 7,
            'North Beach': 24,
            'Financial District': 26,
            'Union Square': 22
        },
        'Union Square': {
            'Presidio': 24,
            'Richmond District': 20,
            'North Beach': 10,
            'Financial District': 9,
            'Golden Gate Park': 22
        }
    }

    # Friend constraints
    friends = {
        'Jason': {
            'location': 'Richmond District',
            'available_start': time_to_minutes('13:00'),  # 1:00 PM
            'available_end': time_to_minutes('20:45'),    # 8:45 PM
            'min_duration': 90
        },
        'Melissa': {
            'location': 'North Beach',
            'available_start': time_to_minutes('18:45'),  # 6:45 PM
            'available_end': time_to_minutes('20:15'),    # 8:15 PM
            'min_duration': 45
        },
        'Brian': {
            'location': 'Financial District',
            'available_start': time_to_minutes('9:45'),   # 9:45 AM
            'available_end': time_to_minutes('21:45'),    # 9:45 PM
            'min_duration': 15
        },
        'Elizabeth': {
            'location': 'Golden Gate Park',
            'available_start': time_to_minutes('8:45'),   # 8:45 AM
            'available_end': time_to_minutes('21:30'),    # 9:30 PM
            'min_duration': 105
        },
        'Laura': {
            'location': 'Union Square',
            'available_start': time_to_minutes('14:15'),  # 2:15 PM
            'available_end': time_to_minutes('19:30'),    # 7:30 PM
            'min_duration': 75
        }
    }

    # Start at Presidio at 9:00 AM
    start_time = time_to_minutes('9:00')
    current_location = 'Presidio'
    max_end_time = time_to_minutes('21:45')  # End of day constraint

    # Create problem
    problem = constraint.Problem()

    # Define variables for each friend: start time and duration
    friend_names = list(friends.keys())
    
    for friend in friend_names:
        info = friends[friend]
        # Start time must be within friend's availability window
        problem.addVariable(f'{friend}_start', range(info['available_start'], info['available_end'] + 1))
        # Duration must be at least the minimum required
        problem.addVariable(f'{friend}_duration', range(info['min_duration'], 
                                                       info['available_end'] - info['available_start'] + 1))

    # Add constraint that meeting must end before friend's availability ends
    for friend in friend_names:
        info = friends[friend]
        def end_time_constraint(start, duration, available_end=info['available_end']):
            return start + duration <= available_end
        problem.addConstraint(end_time_constraint, [f'{friend}_start', f'{friend}_duration'])

    # Define visit order - we'll try all permutations
    from itertools import permutations
    
    best_schedule = None
    max_meetings = 0
    max_total_time = 0
    
    # Try different visit orders
    for order in permutations(friend_names):
        valid_schedule = True
        current_time = start_time
        current_loc = current_location
        schedule = []
        total_meeting_time = 0
        
        for friend in order:
            info = friends[friend]
            
            # Calculate travel time
            travel_time = travel_times[current_loc][info['location']]
            arrival_time = current_time + travel_time
            
            # Check if we can meet this friend
            if arrival_time < info['available_start']:
                meeting_start = info['available_start']
            else:
                meeting_start = arrival_time
            
            # Calculate maximum possible duration
            max_possible_duration = min(info['available_end'] - meeting_start, 
                                      max_end_time - meeting_start)
            
            if max_possible_duration < info['min_duration']:
                valid_schedule = False
                break
            
            # Use maximum possible duration for this friend
            meeting_duration = max_possible_duration
            meeting_end = meeting_start + meeting_duration
            
            if meeting_end > max_end_time:
                valid_schedule = False
                break
            
            schedule.append({
                'friend': friend,
                'location': info['location'],
                'start': meeting_start,
                'end': meeting_end,
                'duration': meeting_duration
            })
            
            total_meeting_time += meeting_duration
            current_time = meeting_end
            current_loc = info['location']
        
        if valid_schedule:
            if len(schedule) > max_meetings or (len(schedule) == max_meetings and total_meeting_time > max_total_time):
                max_meetings = len(schedule)
                max_total_time = total_meeting_time
                best_schedule = schedule
    
    # Format output
    if best_schedule:
        itinerary = []
        for meeting in best_schedule:
            itinerary.append({
                "action": "meet",
                "location": meeting['location'],
                "person": meeting['friend'],
                "start_time": minutes_to_time(meeting['start']),
                "end_time": minutes_to_time(meeting['end'])
            })
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"itinerary": []}, indent=2))

if __name__ == "__main__":
    main()