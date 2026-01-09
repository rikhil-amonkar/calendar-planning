import constraint
from datetime import datetime, timedelta
import json

def main():
    # Travel times in minutes
    travel_times = {
        ('Fisherman\'s Wharf', 'Presidio'): 17,
        ('Fisherman\'s Wharf', 'Richmond District'): 18,
        ('Fisherman\'s Wharf', 'Financial District'): 11,
        ('Presidio', 'Fisherman\'s Wharf'): 19,
        ('Presidio', 'Richmond District'): 7,
        ('Presidio', 'Financial District'): 23,
        ('Richmond District', 'Fisherman\'s Wharf'): 18,
        ('Richmond District', 'Presidio'): 7,
        ('Richmond District', 'Financial District'): 22,
        ('Financial District', 'Fisherman\'s Wharf'): 10,
        ('Financial District', 'Presidio'): 22,
        ('Financial District', 'Richmond District'): 21
    }
    
    # Friend constraints
    friends = {
        'Emily': {
            'location': 'Presidio',
            'available_start': datetime.strptime('16:15', '%H:%M'),
            'available_end': datetime.strptime('21:00', '%H:%M'),
            'min_duration': 105
        },
        'Joseph': {
            'location': 'Richmond District',
            'available_start': datetime.strptime('17:15', '%H:%M'),
            'available_end': datetime.strptime('22:00', '%H:%M'),
            'min_duration': 120
        },
        'Melissa': {
            'location': 'Financial District',
            'available_start': datetime.strptime('15:45', '%H:%M'),
            'available_end': datetime.strptime('21:45', '%H:%M'),
            'min_duration': 75
        }
    }
    
    start_location = 'Fisherman\'s Wharf'
    start_time = datetime.strptime('9:00', '%H:%M')
    
    # Create problem
    problem = constraint.Problem()
    
    # Variables: start times for each meeting (in minutes from 9:00)
    max_time_minutes = 780  # 9:00 AM to 22:00 PM = 13 hours = 780 minutes
    
    for friend in friends:
        problem.addVariable(f'{friend}_start', range(max_time_minutes))
        problem.addVariable(f'{friend}_duration', range(friends[friend]['min_duration'], 
                                                      int((friends[friend]['available_end'] - friends[friend]['available_start']).total_seconds() / 60) + 1))
    
    # Constraint: meetings must be within friend's availability
    def within_availability(friend, start_minutes, duration):
        start_dt = start_time + timedelta(minutes=start_minutes)
        end_dt = start_dt + timedelta(minutes=duration)
        return (start_dt >= friends[friend]['available_start'] and 
                end_dt <= friends[friend]['available_end'])
    
    for friend in friends:
        problem.addConstraint(
            lambda start, dur, f=friend: within_availability(f, start, dur),
            [f'{friend}_start', f'{friend}_duration']
        )
    
    # Constraint: no overlapping meetings and account for travel time
    def no_overlap_and_travel(friends_order):
        def constraint_func(*args):
            # args: start1, dur1, start2, dur2, ..., startN, durN
            meeting_times = []
            for i in range(len(friends_order)):
                start = args[i*2]
                duration = args[i*2 + 1]
                meeting_times.append((friends_order[i], start, duration))
            
            # Sort by start time
            meeting_times.sort(key=lambda x: x[1])
            
            current_location = start_location
            current_time = 0
            
            for i, (friend, start, duration) in enumerate(meeting_times):
                # Check if we can travel to this meeting
                travel_time = travel_times.get((current_location, friends[friend]['location']), 0)
                
                if start < current_time + travel_time:
                    return False
                
                # Update current location and time
                current_location = friends[friend]['location']
                current_time = start + duration
            
            return True
        
        return constraint_func
    
    # Try different meeting orders
    friend_names = list(friends.keys())
    best_solution = None
    best_total_duration = 0
    
    # Generate all possible meeting orders
    from itertools import permutations
    
    for order in permutations(friend_names):
        # Get variable names in this order
        var_names = []
        for friend in order:
            var_names.extend([f'{friend}_start', f'{friend}_duration'])
        
        # Create a temporary problem for this order
        temp_problem = constraint.Problem()
        
        # Copy variables
        for var_name, var_domain in problem._variables.items():
            temp_problem.addVariable(var_name, var_domain)
        
        # Copy constraints
        for constraint_obj in problem._constraints.values():
            temp_problem.addConstraint(constraint_obj, constraint_obj._scope)
        
        # Add ordering constraint
        temp_problem.addConstraint(no_overlap_and_travel(order), var_names)
        
        # Find solutions
        solutions = temp_problem.getSolutions()
        
        for solution in solutions:
            total_duration = sum(solution[f'{friend}_duration'] for friend in friends)
            if total_duration > best_total_duration:
                best_total_duration = total_duration
                best_solution = (solution, order)
    
    # Format output
    if best_solution:
        solution, order = best_solution
        itinerary = []
        
        # Create meeting events in chronological order
        meetings = []
        for friend in friends:
            start_dt = start_time + timedelta(minutes=solution[f'{friend}_start'])
            end_dt = start_dt + timedelta(minutes=solution[f'{friend}_duration'])
            meetings.append({
                'person': friend,
                'location': friends[friend]['location'],
                'start_time': start_dt.strftime('%H:%M'),
                'end_time': end_dt.strftime('%H:%M')
            })
        
        # Sort by start time
        meetings.sort(key=lambda x: datetime.strptime(x['start_time'], '%H:%M'))
        
        # Format itinerary
        for meeting in meetings:
            itinerary.append({
                "action": "meet",
                "location": meeting['location'],
                "person": meeting['person'],
                "start_time": meeting['start_time'],
                "end_time": meeting['end_time']
            })
        
        output = {"itinerary": itinerary}
    else:
        output = {"itinerary": []}
    
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()