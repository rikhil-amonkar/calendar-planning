import json
import itertools
from typing import List, Dict, Any

def time_to_minutes(time_str: str) -> int:
    """Convert time string (H:MM) to minutes since midnight."""
    parts = time_str.split(':')
    hours = int(parts[0])
    minutes = int(parts[1])
    return hours * 60 + minutes

def minutes_to_time(minutes: int) -> str:
    """Convert minutes since midnight to time string (H:MM)."""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    # Define travel times between locations
    travel_times = {
        'Embarcadero': {
            'Richmond District': 21,
            'Union Square': 10,
            'Financial District': 5,
            'Pacific Heights': 11,
            'Nob Hill': 10,
            'Bayview': 21
        },
        'Richmond District': {
            'Embarcadero': 19,
            'Union Square': 21,
            'Financial District': 22,
            'Pacific Heights': 10,
            'Nob Hill': 17,
            'Bayview': 26
        },
        'Union Square': {
            'Embarcadero': 11,
            'Richmond District': 20,
            'Financial District': 9,
            'Pacific Heights': 15,
            'Nob Hill': 9,
            'Bayview': 15
        },
        'Financial District': {
            'Embarcadero': 4,
            'Richmond District': 21,
            'Union Square': 9,
            'Pacific Heights': 13,
            'Nob Hill': 8,
            'Bayview': 19
        },
        'Pacific Heights': {
            'Embarcadero': 10,
            'Richmond District': 12,
            'Union Square': 12,
            'Financial District': 13,
            'Nob Hill': 8,
            'Bayview': 22
        },
        'Nob Hill': {
            'Embarcadero': 9,
            'Richmond District': 14,
            'Union Square': 7,
            'Financial District': 9,
            'Pacific Heights': 8,
            'Bayview': 19
        },
        'Bayview': {
            'Embarcadero': 19,
            'Richmond District': 25,
            'Union Square': 17,
            'Financial District': 19,
            'Pacific Heights': 23,
            'Nob Hill': 20
        }
    }

    # Define friends with their constraints
    friends = [
        {
            'name': 'Kenneth',
            'location': 'Richmond District',
            'available_start': time_to_minutes('21:15'),
            'available_end': time_to_minutes('22:00'),
            'min_duration': 30
        },
        {
            'name': 'Lisa',
            'location': 'Union Square',
            'available_start': time_to_minutes('9:00'),
            'available_end': time_to_minutes('16:30'),
            'min_duration': 45
        },
        {
            'name': 'Joshua',
            'location': 'Financial District',
            'available_start': time_to_minutes('12:00'),
            'available_end': time_to_minutes('15:15'),
            'min_duration': 15
        },
        {
            'name': 'Nancy',
            'location': 'Pacific Heights',
            'available_start': time_to_minutes('8:00'),
            'available_end': time_to_minutes('11:30'),
            'min_duration': 90
        },
        {
            'name': 'Andrew',
            'location': 'Nob Hill',
            'available_start': time_to_minutes('11:30'),
            'available_end': time_to_minutes('20:15'),
            'min_duration': 60
        },
        {
            'name': 'John',
            'location': 'Bayview',
            'available_start': time_to_minutes('16:45'),
            'available_end': time_to_minutes('21:30'),
            'min_duration': 75
        }
    ]

    start_time = time_to_minutes('9:00')
    start_location = 'Embarcadero'
    best_schedule = []
    max_meetings = 0

    # Try all permutations of friends to find optimal schedule
    for num_meetings in range(len(friends), 0, -1):
        for perm in itertools.permutations(friends, num_meetings):
            current_time = start_time
            current_location = start_location
            schedule = []
            valid = True
            
            for friend in perm:
                # Calculate travel time to friend's location
                travel_time = travel_times[current_location][friend['location']]
                arrival_time = current_time + travel_time
                
                # Calculate meeting start and end times
                meeting_start = max(arrival_time, friend['available_start'])
                meeting_end = meeting_start + friend['min_duration']
                
                # Check if meeting fits within available time
                if meeting_end > friend['available_end']:
                    valid = False
                    break
                
                # Add meeting to schedule
                schedule.append({
                    'action': 'meet',
                    'location': friend['location'],
                    'person': friend['name'],
                    'start_time': minutes_to_time(meeting_start),
                    'end_time': minutes_to_time(meeting_end)
                })
                
                current_time = meeting_end
                current_location = friend['location']
            
            if valid and len(schedule) > max_meetings:
                best_schedule = schedule
                max_meetings = len(schedule)
                break
        
        if max_meetings == num_meetings:
            break

    # Output the result as JSON
    result = {
        "itinerary": best_schedule
    }
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()