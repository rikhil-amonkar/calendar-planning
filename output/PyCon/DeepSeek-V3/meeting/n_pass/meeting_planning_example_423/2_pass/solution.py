import constraint
from datetime import datetime, timedelta
import json
from itertools import permutations

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

    best_schedule = None
    max_meetings = 0
    max_total_time = 0
    
    # Try different visit orders
    for order in permutations(friends.keys()):
        current_time = start_time
        current_loc = current_location
        schedule = []
        total_meeting_time = 0
        valid_schedule = True
        
        for friend in order:
            info = friends[friend]
            
            # Calculate travel time to friend's location
            travel_time = travel_times[current_loc][info['location']]
            arrival_time = current_time + travel_time
            
            # Check if we arrive before friend's availability ends
            if arrival_time >= info['available_end']:
                valid_schedule = False
                break
                
            # Determine meeting start time
            meeting_start = max(arrival_time, info['available_start'])
            
            # Check if we have enough time for minimum duration
            if meeting_start + info['min_duration'] > info['available_end']:
                valid_schedule = False
                break
                
            # Calculate maximum possible duration (respecting end of day)
            max_possible_duration = min(
                info['available_end'] - meeting_start,
                max_end_time - meeting_start
            )
            
            # Use the minimum required duration (we can optimize this later)
            meeting_duration = info['min_duration']
            meeting_end = meeting_start + meeting_duration
            
            # Check if meeting fits within constraints
            if meeting_end > max_end_time:
                valid_schedule = False
                break
            
            # Add meeting to schedule
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
        
        # Check if this schedule is better than current best
        if valid_schedule:
            if len(schedule) > max_meetings:
                max_meetings = len(schedule)
                max_total_time = total_meeting_time
                best_schedule = schedule
            elif len(schedule) == max_meetings and total_meeting_time > max_total_time:
                max_total_time = total_meeting_time
                best_schedule = schedule

    # If we found a valid schedule, try to optimize durations
    if best_schedule:
        optimized_schedule = []
        current_time = start_time
        current_loc = current_location
        
        for meeting in best_schedule:
            friend = meeting['friend']
            info = friends[friend]
            
            # Calculate travel time
            travel_time = travel_times[current_loc][info['location']]
            arrival_time = current_time + travel_time
            
            # Determine meeting start time
            meeting_start = max(arrival_time, info['available_start'])
            
            # Calculate maximum possible duration
            max_possible_duration = min(
                info['available_end'] - meeting_start,
                max_end_time - meeting_start
            )
            
            # Use maximum possible duration
            meeting_duration = max_possible_duration
            meeting_end = meeting_start + meeting_duration
            
            optimized_schedule.append({
                'friend': friend,
                'location': info['location'],
                'start': meeting_start,
                'end': meeting_end,
                'duration': meeting_duration
            })
            
            current_time = meeting_end
            current_loc = info['location']
        
        best_schedule = optimized_schedule

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