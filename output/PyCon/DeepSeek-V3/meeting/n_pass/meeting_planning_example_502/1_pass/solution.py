import constraint
import json
from datetime import datetime, timedelta

def time_to_minutes(time_str):
    """Convert time string (H:MM) to minutes since midnight"""
    dt = datetime.strptime(time_str, "%H:%M")
    return dt.hour * 60 + dt.minute

def minutes_to_time(minutes):
    """Convert minutes since midnight to time string (H:MM)"""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    # Travel times in minutes (from_location, to_location): time
    travel_times = {
        ('Financial District', 'Golden Gate Park'): 23,
        ('Financial District', 'Chinatown'): 5,
        ('Financial District', 'Union Square'): 9,
        ('Financial District', 'Fisherman\'s Wharf'): 10,
        ('Financial District', 'Pacific Heights'): 13,
        ('Financial District', 'North Beach'): 7,
        ('Golden Gate Park', 'Financial District'): 26,
        ('Golden Gate Park', 'Chinatown'): 23,
        ('Golden Gate Park', 'Union Square'): 22,
        ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
        ('Golden Gate Park', 'Pacific Heights'): 16,
        ('Golden Gate Park', 'North Beach'): 24,
        ('Chinatown', 'Financial District'): 5,
        ('Chinatown', 'Golden Gate Park'): 23,
        ('Chinatown', 'Union Square'): 7,
        ('Chinatown', 'Fisherman\'s Wharf'): 8,
        ('Chinatown', 'Pacific Heights'): 10,
        ('Chinatown', 'North Beach'): 3,
        ('Union Square', 'Financial District'): 9,
        ('Union Square', 'Golden Gate Park'): 22,
        ('Union Square', 'Chinatown'): 7,
        ('Union Square', 'Fisherman\'s Wharf'): 15,
        ('Union Square', 'Pacific Heights'): 15,
        ('Union Square', 'North Beach'): 10,
        ('Fisherman\'s Wharf', 'Financial District'): 11,
        ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
        ('Fisherman\'s Wharf', 'Chinatown'): 12,
        ('Fisherman\'s Wharf', 'Union Square'): 13,
        ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
        ('Fisherman\'s Wharf', 'North Beach'): 6,
        ('Pacific Heights', 'Financial District'): 13,
        ('Pacific Heights', 'Golden Gate Park'): 15,
        ('Pacific Heights', 'Chinatown'): 11,
        ('Pacific Heights', 'Union Square'): 12,
        ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
        ('Pacific Heights', 'North Beach'): 9,
        ('North Beach', 'Financial District'): 8,
        ('North Beach', 'Golden Gate Park'): 22,
        ('North Beach', 'Chinatown'): 6,
        ('North Beach', 'Union Square'): 7,
        ('North Beach', 'Fisherman\'s Wharf'): 5,
        ('North Beach', 'Pacific Heights'): 8
    }
    
    # Friend constraints
    friends = {
        'Stephanie': {
            'location': 'Golden Gate Park',
            'available_start': time_to_minutes('11:00'),
            'available_end': time_to_minutes('15:00'),
            'min_duration': 105
        },
        'Karen': {
            'location': 'Chinatown',
            'available_start': time_to_minutes('13:45'),
            'available_end': time_to_minutes('16:30'),
            'min_duration': 15
        },
        'Brian': {
            'location': 'Union Square',
            'available_start': time_to_minutes('15:00'),
            'available_end': time_to_minutes('17:15'),
            'min_duration': 30
        },
        'Rebecca': {
            'location': 'Fisherman\'s Wharf',
            'available_start': time_to_minutes('8:00'),
            'available_end': time_to_minutes('11:15'),
            'min_duration': 30
        },
        'Joseph': {
            'location': 'Pacific Heights',
            'available_start': time_to_minutes('8:15'),
            'available_end': time_to_minutes('9:30'),
            'min_duration': 60
        },
        'Steven': {
            'location': 'North Beach',
            'available_start': time_to_minutes('14:30'),
            'available_end': time_to_minutes('20:45'),
            'min_duration': 120
        }
    }
    
    # Start at Financial District at 9:00 AM
    current_time = time_to_minutes('9:00')
    current_location = 'Financial District'
    
    problem = constraint.Problem()
    
    # Define variables for each friend: (start_time, duration)
    for friend in friends:
        friend_info = friends[friend]
        min_start = max(friend_info['available_start'], current_time)
        max_start = friend_info['available_end'] - friend_info['min_duration']
        
        if min_start <= max_start:
            problem.addVariable(f"{friend}_start", range(min_start, max_start + 1))
            problem.addVariable(f"{friend}_duration", [friend_info['min_duration']])
        else:
            # If no valid time window, set to None
            problem.addVariable(f"{friend}_start", [None])
            problem.addVariable(f"{friend}_duration", [0])
    
    # Define meeting order as a permutation of friends we can actually meet
    valid_friends = [f for f in friends if friends[f]['available_end'] - max(friends[f]['available_start'], current_time) >= friends[f]['min_duration']]
    problem.addVariable("meeting_order", [valid_friends])
    
    def travel_constraint(*args):
        # Extract all start times and durations
        meeting_data = {}
        for i, friend in enumerate(valid_friends):
            meeting_data[friend] = {
                'start': args[i * 2],
                'duration': args[i * 2 + 1]
            }
        
        # Check if we can visit all meetings in the order with travel times
        current_loc = current_location
        current_time_val = current_time
        
        for friend in valid_friends:
            if meeting_data[friend]['start'] is None:
                continue
                
            # Check if we have enough time to travel to this meeting
            travel_time = travel_times.get((current_loc, friends[friend]['location']), 60)
            
            # Arrival time at meeting
            arrival_time = current_time_val + travel_time
            
            # We must arrive before or at the meeting start time
            if arrival_time > meeting_data[friend]['start']:
                return False
            
            # Update current time and location
            current_time_val = meeting_data[friend]['start'] + meeting_data[friend]['duration']
            current_loc = friends[friend]['location']
        
        return True
    
    # Add constraint for travel times
    all_vars = []
    for friend in valid_friends:
        all_vars.extend([f"{friend}_start", f"{friend}_duration"])
    
    if all_vars:
        problem.addConstraint(travel_constraint, all_vars)
    
    # Find a solution
    solutions = problem.getSolutions()
    
    if not solutions:
        # If no solution found, try to meet as many friends as possible
        best_solution = None
        max_meetings = 0
        
        # Simple greedy approach: meet friends in chronological order of availability
        itinerary = []
        current_time_val = current_time
        current_loc = current_location
        
        # Sort friends by available start time
        sorted_friends = sorted([f for f in friends], key=lambda x: friends[x]['available_start'])
        
        for friend in sorted_friends:
            friend_info = friends[friend]
            
            # Calculate earliest possible start time
            travel_time = travel_times.get((current_loc, friend_info['location']), 60)
            earliest_start = max(friend_info['available_start'], current_time_val + travel_time)
            
            # Check if we can meet this friend
            if earliest_start + friend_info['min_duration'] <= friend_info['available_end']:
                # Schedule the meeting
                start_time = earliest_start
                end_time = start_time + friend_info['min_duration']
                
                itinerary.append({
                    "action": "meet",
                    "location": friend_info['location'],
                    "person": friend,
                    "start_time": minutes_to_time(start_time),
                    "end_time": minutes_to_time(end_time)
                })
                
                current_time_val = end_time
                current_loc = friend_info['location']
        
        result = {"itinerary": itinerary}
    else:
        # Use the first solution found
        solution = solutions[0]
        itinerary = []
        
        # Sort meetings by start time
        meetings = []
        for friend in valid_friends:
            if solution.get(f"{friend}_start") is not None:
                meetings.append({
                    'friend': friend,
                    'start': solution[f"{friend}_start"],
                    'duration': solution[f"{friend}_duration"],
                    'location': friends[friend]['location']
                })
        
        meetings.sort(key=lambda x: x['start'])
        
        for meeting in meetings:
            itinerary.append({
                "action": "meet",
                "location": meeting['location'],
                "person": meeting['friend'],
                "start_time": minutes_to_time(meeting['start']),
                "end_time": minutes_to_time(meeting['start'] + meeting['duration'])
            })
        
        result = {"itinerary": itinerary}
    
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()