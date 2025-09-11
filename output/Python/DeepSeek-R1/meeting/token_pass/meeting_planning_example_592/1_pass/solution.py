import itertools
import json

def main():
    # Define travel times between locations
    travel_times = {
        'North Beach': {
            'North Beach': 0,
            'Pacific Heights': 8,
            'Chinatown': 6,
            'Union Square': 7,
            'Mission District': 18,
            'Golden Gate Park': 22,
            'Nob Hill': 7
        },
        'Pacific Heights': {
            'North Beach': 9,
            'Pacific Heights': 0,
            'Chinatown': 11,
            'Union Square': 12,
            'Mission District': 15,
            'Golden Gate Park': 15,
            'Nob Hill': 8
        },
        'Chinatown': {
            'North Beach': 3,
            'Pacific Heights': 10,
            'Chinatown': 0,
            'Union Square': 7,
            'Mission District': 18,
            'Golden Gate Park': 23,
            'Nob Hill': 8
        },
        'Union Square': {
            'North Beach': 10,
            'Pacific Heights': 15,
            'Chinatown': 7,
            'Union Square': 0,
            'Mission District': 14,
            'Golden Gate Park': 22,
            'Nob Hill': 9
        },
        'Mission District': {
            'North Beach': 17,
            'Pacific Heights': 16,
            'Chinatown': 16,
            'Union Square': 15,
            'Mission District': 0,
            'Golden Gate Park': 17,
            'Nob Hill': 12
        },
        'Golden Gate Park': {
            'North Beach': 24,
            'Pacific Heights': 16,
            'Chinatown': 23,
            'Union Square': 22,
            'Mission District': 17,
            'Golden Gate Park': 0,
            'Nob Hill': 20
        },
        'Nob Hill': {
            'North Beach': 8,
            'Pacific Heights': 8,
            'Chinatown': 6,
            'Union Square': 7,
            'Mission District': 13,
            'Golden Gate Park': 17,
            'Nob Hill': 0
        }
    }
    
    # Convert time strings to minutes since 9:00 AM
    def time_to_minutes(time_str):
        hours, minutes = map(int, time_str.split(':'))
        return (hours - 9) * 60 + minutes
    
    # Convert minutes since 9:00 AM to time string
    def minutes_to_time(minutes):
        total_minutes = 9 * 60 + minutes
        h = total_minutes // 60
        m = total_minutes % 60
        return f"{h}:{m:02d}"
    
    # Define friends with their constraints
    friends = [
        {
            'name': 'James',
            'location': 'Pacific Heights',
            'start': time_to_minutes('20:00'),  # 8:00 PM
            'end': time_to_minutes('22:00'),    # 10:00 PM
            'min_duration': 120
        },
        {
            'name': 'Robert',
            'location': 'Chinatown',
            'start': time_to_minutes('12:15'),  # 12:15 PM
            'end': time_to_minutes('16:45'),    # 4:45 PM
            'min_duration': 90
        },
        {
            'name': 'Jeffrey',
            'location': 'Union Square',
            'start': time_to_minutes('9:30'),   # 9:30 AM
            'end': time_to_minutes('15:30'),    # 3:30 PM
            'min_duration': 120
        },
        {
            'name': 'Carol',
            'location': 'Mission District',
            'start': time_to_minutes('18:15'),  # 6:15 PM
            'end': time_to_minutes('21:15'),    # 9:15 PM
            'min_duration': 15
        },
        {
            'name': 'Mark',
            'location': 'Golden Gate Park',
            'start': time_to_minutes('11:30'),  # 11:30 AM
            'end': time_to_minutes('17:45'),    # 5:45 PM
            'min_duration': 15
        },
        {
            'name': 'Sandra',
            'location': 'Nob Hill',
            'start': time_to_minutes('9:00'),   # 9:00 AM (available from 8:00 but we start at 9:00)
            'end': time_to_minutes('15:30'),    # 3:30 PM
            'min_duration': 15
        }
    ]
    
    best_count = 0
    best_schedule = []
    
    # Try all permutations of friends to find optimal schedule
    for perm in itertools.permutations(friends):
        current_time = 0
        current_location = 'North Beach'
        schedule = []
        count = 0
        
        for friend in perm:
            loc = friend['location']
            travel_time = travel_times[current_location][loc]
            arrival_time = current_time + travel_time
            
            # Check if we can meet within the friend's window
            start_meeting = max(arrival_time, friend['start'])
            end_meeting = start_meeting + friend['min_duration']
            
            if end_meeting <= friend['end']:
                # Meeting is possible
                count += 1
                schedule.append({
                    'action': 'meet',
                    'location': loc,
                    'person': friend['name'],
                    'start_time': minutes_to_time(start_meeting),
                    'end_time': minutes_to_time(end_meeting)
                })
                current_time = end_meeting
                current_location = loc
            else:
                # Skip friend if meeting isn't possible
                continue
                
        # Update best schedule if this permutation has more meetings
        if count > best_count:
            best_count = count
            best_schedule = schedule
    
    # Output the best schedule as JSON
    result = {
        "itinerary": best_schedule
    }
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()