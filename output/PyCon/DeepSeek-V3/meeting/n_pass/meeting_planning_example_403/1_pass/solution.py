import constraint
import json
from datetime import datetime, timedelta

def time_to_minutes(time_str):
    """Convert time string (H:MM) to minutes since midnight"""
    if isinstance(time_str, str):
        dt = datetime.strptime(time_str, '%H:%M')
    else:
        dt = time_str
    return dt.hour * 60 + dt.minute

def minutes_to_time(minutes):
    """Convert minutes since midnight to time string (H:MM)"""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    # Travel times in minutes (symmetric matrix)
    travel_times = {
        'Union Square': {
            'Union Square': 0, 'Golden Gate Park': 22, 'Pacific Heights': 15, 
            'Presidio': 24, 'Chinatown': 7, 'The Castro': 19
        },
        'Golden Gate Park': {
            'Union Square': 22, 'Golden Gate Park': 0, 'Pacific Heights': 16, 
            'Presidio': 11, 'Chinatown': 23, 'The Castro': 13
        },
        'Pacific Heights': {
            'Union Square': 12, 'Golden Gate Park': 15, 'Pacific Heights': 0, 
            'Presidio': 11, 'Chinatown': 11, 'The Castro': 16
        },
        'Presidio': {
            'Union Square': 22, 'Golden Gate Park': 12, 'Pacific Heights': 11, 
            'Presidio': 0, 'Chinatown': 21, 'The Castro': 21
        },
        'Chinatown': {
            'Union Square': 7, 'Golden Gate Park': 23, 'Pacific Heights': 10, 
            'Presidio': 19, 'Chinatown': 0, 'The Castro': 22
        },
        'The Castro': {
            'Union Square': 19, 'Golden Gate Park': 11, 'Pacific Heights': 16, 
            'Presidio': 20, 'Chinatown': 20, 'The Castro': 0
        }
    }
    
    # Friend constraints
    friends = {
        'Andrew': {
            'location': 'Golden Gate Park',
            'available_start': time_to_minutes('11:45'),
            'available_end': time_to_minutes('14:30'),
            'min_duration': 75
        },
        'Sarah': {
            'location': 'Pacific Heights',
            'available_start': time_to_minutes('16:15'),
            'available_end': time_to_minutes('18:45'),
            'min_duration': 15
        },
        'Nancy': {
            'location': 'Presidio',
            'available_start': time_to_minutes('17:30'),
            'available_end': time_to_minutes('19:15'),
            'min_duration': 60
        },
        'Rebecca': {
            'location': 'Chinatown',
            'available_start': time_to_minutes('9:45'),
            'available_end': time_to_minutes('21:30'),
            'min_duration': 90
        },
        'Robert': {
            'location': 'The Castro',
            'available_start': time_to_minutes('8:30'),
            'available_end': time_to_minutes('14:15'),
            'min_duration': 30
        }
    }
    
    # Start at Union Square at 9:00 AM
    start_time = time_to_minutes('9:00')
    current_location = 'Union Square'
    
    problem = constraint.Problem()
    
    # Variables: start time and duration for each friend
    for friend in friends:
        friend_info = friends[friend]
        available_start = friend_info['available_start']
        available_end = friend_info['available_end']
        min_duration = friend_info['min_duration']
        
        # Start time must be within friend's availability window
        problem.addVariable(f'{friend}_start', range(available_start, available_end - min_duration + 1))
        # Duration must be at least the minimum required
        problem.addVariable(f'{friend}_duration', range(min_duration, available_end - available_start + 1))
    
    # Helper function to check if we can meet a friend
    def can_meet_friend(friend, start_time, duration, prev_location, prev_end_time):
        if start_time < prev_end_time + travel_times[prev_location][friends[friend]['location']]:
            return False
        
        end_time = start_time + duration
        if end_time > friends[friend]['available_end']:
            return False
        
        return True
    
    # Define the constraint function
    def meeting_constraints(*args):
        # Extract all variables
        variables = {}
        for i, friend in enumerate(friends):
            variables[f'{friend}_start'] = args[i * 2]
            variables[f'{friend}_duration'] = args[i * 2 + 1]
        
        # Create a list of meetings with their details
        meetings = []
        for friend in friends:
            start = variables[f'{friend}_start']
            duration = variables[f'{friend}_duration']
            end = start + duration
            location = friends[friend]['location']
            
            # Check if meeting fits within friend's availability
            if start < friends[friend]['available_start'] or end > friends[friend]['available_end']:
                return False
            
            meetings.append((friend, start, duration, end, location))
        
        # Sort meetings by start time
        meetings.sort(key=lambda x: x[1])
        
        # Check travel feasibility between meetings
        current_time = start_time
        current_loc = current_location
        
        for meeting in meetings:
            friend, start, duration, end, location = meeting
            
            # Check if we can travel to this meeting in time
            travel_time = travel_times[current_loc][location]
            if start < current_time + travel_time:
                return False
            
            # Update current time and location
            current_time = end
            current_loc = location
        
        return True
    
    # Add the constraint
    all_vars = []
    for friend in friends:
        all_vars.append(f'{friend}_start')
        all_vars.append(f'{friend}_duration')
    
    problem.addConstraint(meeting_constraints, all_vars)
    
    # Find a solution
    solutions = problem.getSolutions()
    
    if not solutions:
        # If no solution found, try with fewer constraints
        # For simplicity, we'll create a reasonable schedule manually
        itinerary = []
        current_time = start_time
        current_loc = current_location
        
        # Try to meet Rebecca first (earliest availability)
        rebecca = friends['Rebecca']
        travel_time = travel_times[current_loc][rebecca['location']]
        meet_start = max(current_time + travel_time, rebecca['available_start'])
        meet_end = meet_start + rebecca['min_duration']
        
        if meet_end <= rebecca['available_end']:
            itinerary.append({
                'action': 'meet',
                'location': rebecca['location'],
                'person': 'Rebecca',
                'start_time': minutes_to_time(meet_start),
                'end_time': minutes_to_time(meet_end)
            })
            current_time = meet_end
            current_loc = rebecca['location']
        
        # Try to meet Andrew next
        andrew = friends['Andrew']
        travel_time = travel_times[current_loc][andrew['location']]
        meet_start = max(current_time + travel_time, andrew['available_start'])
        meet_end = meet_start + andrew['min_duration']
        
        if meet_end <= andrew['available_end']:
            itinerary.append({
                'action': 'meet',
                'location': andrew['location'],
                'person': 'Andrew',
                'start_time': minutes_to_time(meet_start),
                'end_time': minutes_to_time(meet_end)
            })
            current_time = meet_end
            current_loc = andrew['location']
        
        # Try to meet Sarah
        sarah = friends['Sarah']
        travel_time = travel_times[current_loc][sarah['location']]
        meet_start = max(current_time + travel_time, sarah['available_start'])
        meet_end = meet_start + sarah['min_duration']
        
        if meet_end <= sarah['available_end']:
            itinerary.append({
                'action': 'meet',
                'location': sarah['location'],
                'person': 'Sarah',
                'start_time': minutes_to_time(meet_start),
                'end_time': minutes_to_time(meet_end)
            })
            current_time = meet_end
            current_loc = sarah['location']
        
        # Try to meet Nancy
        nancy = friends['Nancy']
        travel_time = travel_times[current_loc][nancy['location']]
        meet_start = max(current_time + travel_time, nancy['available_start'])
        meet_end = meet_start + nancy['min_duration']
        
        if meet_end <= nancy['available_end']:
            itinerary.append({
                'action': 'meet',
                'location': nancy['location'],
                'person': 'Nancy',
                'start_time': minutes_to_time(meet_start),
                'end_time': minutes_to_time(meet_end)
            })
        
        result = {'itinerary': itinerary}
    else:
        # Use the first solution found
        solution = solutions[0]
        
        # Create meetings list
        meetings = []
        for friend in friends:
            start = solution[f'{friend}_start']
            duration = solution[f'{friend}_duration']
            location = friends[friend]['location']
            
            meetings.append({
                'friend': friend,
                'start': start,
                'duration': duration,
                'end': start + duration,
                'location': location
            })
        
        # Sort by start time
        meetings.sort(key=lambda x: x['start'])
        
        # Build itinerary
        itinerary = []
        for meeting in meetings:
            itinerary.append({
                'action': 'meet',
                'location': meeting['location'],
                'person': meeting['friend'],
                'start_time': minutes_to_time(meeting['start']),
                'end_time': minutes_to_time(meeting['end'])
            })
        
        result = {'itinerary': itinerary}
    
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()