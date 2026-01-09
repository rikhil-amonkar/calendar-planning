import constraint
import json
from datetime import datetime, timedelta
import itertools

def time_to_minutes(time_str):
    """Convert time string (H:MM) to minutes since midnight"""
    if isinstance(time_str, str):
        dt = datetime.strptime(time_str, "%H:%M")
    else:
        dt = time_str
    return dt.hour * 60 + dt.minute

def minutes_to_time(minutes):
    """Convert minutes since midnight to time string (H:MM)"""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    # Travel times matrix (in minutes)
    travel_times = {
        'Presidio': {
            'Golden Gate Park': 12, 'Bayview': 31, 'Chinatown': 21, 
            'North Beach': 18, 'Mission District': 26
        },
        'Golden Gate Park': {
            'Presidio': 11, 'Bayview': 23, 'Chinatown': 23, 
            'North Beach': 24, 'Mission District': 17
        },
        'Bayview': {
            'Presidio': 31, 'Golden Gate Park': 22, 'Chinatown': 18, 
            'North Beach': 21, 'Mission District': 13
        },
        'Chinatown': {
            'Presidio': 19, 'Golden Gate Park': 23, 'Bayview': 22, 
            'North Beach': 3, 'Mission District': 18
        },
        'North Beach': {
            'Presidio': 17, 'Golden Gate Park': 22, 'Bayview': 22, 
            'Chinatown': 6, 'Mission District': 18
        },
        'Mission District': {
            'Presidio': 25, 'Golden Gate Park': 17, 'Bayview': 15, 
            'Chinatown': 16, 'North Beach': 17
        }
    }

    # Friend constraints
    friends = {
        'Jessica': {
            'location': 'Golden Gate Park',
            'available_start': time_to_minutes('13:45'),  # 1:45 PM
            'available_end': time_to_minutes('15:00'),    # 3:00 PM
            'min_duration': 30
        },
        'Ashley': {
            'location': 'Bayview',
            'available_start': time_to_minutes('17:15'),  # 5:15 PM
            'available_end': time_to_minutes('20:00'),    # 8:00 PM
            'min_duration': 105
        },
        'Ronald': {
            'location': 'Chinatown',
            'available_start': time_to_minutes('7:15'),   # 7:15 AM
            'available_end': time_to_minutes('14:45'),    # 2:45 PM
            'min_duration': 90
        },
        'William': {
            'location': 'North Beach',
            'available_start': time_to_minutes('13:15'),  # 1:15 PM
            'available_end': time_to_minutes('20:15'),    # 8:15 PM
            'min_duration': 15
        },
        'Daniel': {
            'location': 'Mission District',
            'available_start': time_to_minutes('7:00'),   # 7:00 AM
            'available_end': time_to_minutes('11:15'),    # 11:15 AM
            'min_duration': 105
        }
    }

    # Start at Presidio at 9:00 AM
    start_time = time_to_minutes('9:00')
    start_location = 'Presidio'

    # Create problem
    problem = constraint.Problem()

    # Variables: start time and duration for each friend
    friend_names = list(friends.keys())
    
    for friend in friend_names:
        info = friends[friend]
        # Start time must be within available window
        problem.addVariable(f'{friend}_start', range(info['available_start'], info['available_end'] + 1))
        # Duration must be at least minimum required
        problem.addVariable(f'{friend}_duration', range(info['min_duration'], 
                                                       info['available_end'] - info['available_start'] + 1))

    # Add constraint that meeting cannot exceed available time
    for friend in friend_names:
        info = friends[friend]
        def meeting_fits_window(friend_start, friend_duration, f=friend, i=info):
            return friend_start + friend_duration <= i['available_end']
        problem.addConstraint(meeting_fits_window, [f'{friend}_start', f'{friend}_duration'])

    # Generate all possible permutations for visit order
    all_permutations = list(itertools.permutations(friend_names))
    problem.addVariable('visit_order', all_permutations)

    # Travel time constraints
    def travel_constraint(*args):
        # Extract all variables
        visit_order = args[-1]
        start_times = {}
        durations = {}
        locations = {}
        
        for i, friend in enumerate(friend_names):
            start_times[friend] = args[i]
            durations[friend] = args[i + len(friend_names)]
            locations[friend] = friends[friend]['location']
        
        current_time = start_time
        current_location = start_location
        
        for friend in visit_order:
            # Travel time to friend's location
            travel_time = travel_times[current_location][locations[friend]]
            
            # Arrival time at friend's location
            arrival_time = current_time + travel_time
            
            # Meeting must start after arrival and within friend's availability
            meeting_start = start_times[friend]
            if meeting_start < arrival_time:
                return False
            
            # Meeting end time
            meeting_end = meeting_start + durations[friend]
            
            # Update for next iteration
            current_time = meeting_end
            current_location = locations[friend]
        
        return True

    # Build argument list for constraint
    constraint_args = []
    for friend in friend_names:
        constraint_args.append(f'{friend}_start')
    for friend in friend_names:
        constraint_args.append(f'{friend}_duration')
    constraint_args.append('visit_order')
    
    problem.addConstraint(travel_constraint, constraint_args)

    # Objective: maximize total meeting time
    def objective(*args):
        total_duration = 0
        for i in range(len(friend_names), 2 * len(friend_names)):
            total_duration += args[i]
        return total_duration

    # Find solution
    solutions = problem.getSolutions()
    
    if not solutions:
        # Fallback: try to meet as many friends as possible with minimum durations
        best_solution = None
        best_score = -1
        
        for friend in friend_names:
            # Try meeting just this one friend
            info = friends[friend]
            
            # Calculate earliest possible start considering travel from Presidio
            travel_time = travel_times[start_location][info['location']]
            earliest_start = max(info['available_start'], start_time + travel_time)
            
            if earliest_start <= info['available_end'] - info['min_duration']:
                # Can meet this friend
                meeting_start = earliest_start
                meeting_duration = min(info['min_duration'], info['available_end'] - meeting_start)
                
                if meeting_duration > best_score:
                    best_score = meeting_duration
                    best_solution = {
                        'visit_order': [friend],
                        f'{friend}_start': meeting_start,
                        f'{friend}_duration': meeting_duration
                    }
        
        if best_solution:
            solution = best_solution
        else:
            # No meetings possible
            solution = {'visit_order': []}
    else:
        # Find solution with maximum total meeting time
        solution = max(solutions, key=objective)

    # Build itinerary
    itinerary = []
    current_time = start_time
    current_location = start_location
    
    for friend in solution['visit_order']:
        friend_start = solution[f'{friend}_start']
        friend_duration = solution[f'{friend}_duration']
        friend_location = friends[friend]['location']
        
        # Add travel if needed
        if current_location != friend_location:
            travel_time = travel_times[current_location][friend_location]
            travel_start = minutes_to_time(current_time)
            travel_end = minutes_to_time(current_time + travel_time)
            itinerary.append({
                "action": "travel",
                "from": current_location,
                "to": friend_location,
                "start_time": travel_start,
                "end_time": travel_end
            })
            current_time += travel_time
        
        # Add meeting
        meeting_start = minutes_to_time(friend_start)
        meeting_end = minutes_to_time(friend_start + friend_duration)
        itinerary.append({
            "action": "meet",
            "location": friend_location,
            "person": friend,
            "start_time": meeting_start,
            "end_time": meeting_end
        })
        
        current_time = friend_start + friend_duration
        current_location = friend_location

    # Output result
    result = {
        "itinerary": itinerary
    }
    
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()