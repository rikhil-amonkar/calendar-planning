from constraint import Problem
import json

def time_to_minutes(time_str):
    """Convert time string (H:MM) to minutes since midnight"""
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    """Convert minutes since midnight to time string (H:MM)"""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    # Travel times in minutes
    travel_times = {
        ('Financial District', 'Fisherman\'s Wharf'): 10,
        ('Financial District', 'Pacific Heights'): 13,
        ('Financial District', 'Mission District'): 17,
        ('Fisherman\'s Wharf', 'Financial District'): 11,
        ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
        ('Fisherman\'s Wharf', 'Mission District'): 22,
        ('Pacific Heights', 'Financial District'): 13,
        ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
        ('Pacific Heights', 'Mission District'): 15,
        ('Mission District', 'Financial District'): 17,
        ('Mission District', 'Fisherman\'s Wharf'): 22,
        ('Mission District', 'Pacific Heights'): 16
    }
    
    # Convert all times to minutes since midnight
    start_time_fd = time_to_minutes('9:00')
    
    # Friend constraints (in minutes since midnight)
    david_available_start = time_to_minutes('10:45')
    david_available_end = time_to_minutes('15:30')
    david_min_duration = 15
    
    timothy_available_start = time_to_minutes('9:00')
    timothy_available_end = time_to_minutes('15:30')
    timothy_min_duration = 75
    
    robert_available_start = time_to_minutes('12:15')
    robert_available_end = time_to_minutes('19:45')
    robert_min_duration = 90
    
    # Create constraint problem
    problem = Problem()
    
    # Define variables for meeting start times and durations
    # We'll try to meet all three friends in some order
    friends = ['David', 'Timothy', 'Robert']
    
    # Variables for start times (in minutes since midnight)
    problem.addVariable('david_start', range(david_available_start, david_available_end - david_min_duration + 1))
    problem.addVariable('timothy_start', range(timothy_available_start, timothy_available_end - timothy_min_duration + 1))
    problem.addVariable('robert_start', range(robert_available_start, robert_available_end - robert_min_duration + 1))
    
    # Variables for durations (minimum to maximum possible)
    problem.addVariable('david_duration', [david_min_duration])
    problem.addVariable('timothy_duration', [timothy_min_duration])
    problem.addVariable('robert_duration', [robert_min_duration])
    
    # Variable for meeting order (permutation of friends)
    problem.addVariable('order', [
        ['David', 'Timothy', 'Robert'],
        ['David', 'Robert', 'Timothy'],
        ['Timothy', 'David', 'Robert'],
        ['Timothy', 'Robert', 'David'],
        ['Robert', 'David', 'Timothy'],
        ['Robert', 'Timothy', 'David']
    ])
    
    def meeting_constraints(david_start, timothy_start, robert_start, 
                           david_duration, timothy_duration, robert_duration, order):
        # Calculate end times
        david_end = david_start + david_duration
        timothy_end = timothy_start + timothy_duration
        robert_end = robert_start + robert_duration
        
        # Check if meetings fit within available windows
        if not (david_available_start <= david_start and david_end <= david_available_end):
            return False
        if not (timothy_available_start <= timothy_start and timothy_end <= timothy_available_end):
            return False
        if not (robert_available_start <= robert_start and robert_end <= robert_available_end):
            return False
        
        # Get locations
        locations = {
            'David': 'Fisherman\'s Wharf',
            'Timothy': 'Pacific Heights', 
            'Robert': 'Mission District'
        }
        
        # Check travel feasibility based on order
        current_time = start_time_fd
        current_location = 'Financial District'
        
        for friend in order:
            target_location = locations[friend]
            travel_time = travel_times.get((current_location, target_location), 999)
            
            # Check if we can reach the meeting on time
            if friend == 'David':
                meeting_start = david_start
            elif friend == 'Timothy':
                meeting_start = timothy_start
            else:  # Robert
                meeting_start = robert_start
                
            if current_time + travel_time > meeting_start:
                return False
                
            # Update current time and location
            if friend == 'David':
                current_time = david_end
            elif friend == 'Timothy':
                current_time = timothy_end
            else:  # Robert
                current_time = robert_end
            current_location = target_location
        
        return True
    
    problem.addConstraint(meeting_constraints, 
                         ['david_start', 'timothy_start', 'robert_start',
                          'david_duration', 'timothy_duration', 'robert_duration', 'order'])
    
    # Find a solution
    solutions = problem.getSolutions()
    
    if not solutions:
        # If no solution found for all three, try with two friends
        best_solution = None
        best_meeting_count = 0
        
        # Try all combinations of two friends
        for friend_combinations in [
            ['David', 'Timothy'],
            ['David', 'Robert'],
            ['Timothy', 'Robert']
        ]:
            problem2 = Problem()
            
            vars_to_include = {}
            if 'David' in friend_combinations:
                problem2.addVariable('david_start', range(david_available_start, david_available_end - david_min_duration + 1))
                problem2.addVariable('david_duration', [david_min_duration])
                vars_to_include['David'] = ('david_start', 'david_duration')
            
            if 'Timothy' in friend_combinations:
                problem2.addVariable('timothy_start', range(timothy_available_start, timothy_available_end - timothy_min_duration + 1))
                problem2.addVariable('timothy_duration', [timothy_min_duration])
                vars_to_include['Timothy'] = ('timothy_start', 'timothy_duration')
            
            if 'Robert' in friend_combinations:
                problem2.addVariable('robert_start', range(robert_available_start, robert_available_end - robert_min_duration + 1))
                problem2.addVariable('robert_duration', [robert_min_duration])
                vars_to_include['Robert'] = ('robert_start', 'robert_duration')
            
            # Generate all possible orders with the available friends
            from itertools import permutations
            possible_orders = list(permutations(friend_combinations))
            problem2.addVariable('order', possible_orders)
            
            def two_friend_constraint(*args):
                arg_dict = {}
                order = args[-1]
                idx = 0
                
                for friend in friend_combinations:
                    var_names = vars_to_include[friend]
                    arg_dict[var_names[0]] = args[idx]
                    arg_dict[var_names[1]] = args[idx + 1]
                    idx += 2
                
                return meeting_constraints(
                    arg_dict.get('david_start', 0),
                    arg_dict.get('timothy_start', 0), 
                    arg_dict.get('robert_start', 0),
                    arg_dict.get('david_duration', 0),
                    arg_dict.get('timothy_duration', 0),
                    arg_dict.get('robert_duration', 0),
                    order
                )
            
            all_vars = []
            for friend in friend_combinations:
                all_vars.extend(vars_to_include[friend])
            all_vars.append('order')
            
            problem2.addConstraint(two_friend_constraint, all_vars)
            solutions2 = problem2.getSolutions()
            
            if solutions2 and len(friend_combinations) > best_meeting_count:
                best_solution = solutions2[0]
                best_meeting_count = len(friend_combinations)
        
        if best_solution:
            solution = best_solution
        else:
            # If still no solution, create a default with one meeting
            solution = {
                'david_start': david_available_start,
                'david_duration': david_min_duration,
                'timothy_start': timothy_available_start, 
                'timothy_duration': timothy_min_duration,
                'robert_start': robert_available_start,
                'robert_duration': robert_min_duration,
                'order': ['Timothy']  # Default to Timothy since he's available longest
            }
    else:
        solution = solutions[0]
    
    # Build itinerary
    itinerary = []
    current_time = start_time_fd
    current_location = 'Financial District'
    
    locations = {
        'David': 'Fisherman\'s Wharf',
        'Timothy': 'Pacific Heights',
        'Robert': 'Mission District'
    }
    
    # Add travel from Financial District to first meeting
    first_friend = solution['order'][0]
    first_location = locations[first_friend]
    travel_time = travel_times[(current_location, first_location)]
    
    # Add meetings in order
    for friend in solution['order']:
        location = locations[friend]
        
        # Add travel segment if needed
        if current_location != location:
            travel_time = travel_times.get((current_location, location), 0)
            travel_start = current_time
            travel_end = current_time + travel_time
            itinerary.append({
                "action": "travel",
                "location": location,
                "person": "",
                "start_time": minutes_to_time(travel_start),
                "end_time": minutes_to_time(travel_end)
            })
            current_time = travel_end
            current_location = location
        
        # Add meeting
        if friend == 'David':
            start_time = solution['david_start']
            duration = solution['david_duration']
        elif friend == 'Timothy':
            start_time = solution['timothy_start']
            duration = solution['timothy_duration']
        else:  # Robert
            start_time = solution['robert_start']
            duration = solution['robert_duration']
        
        end_time = start_time + duration
        
        itinerary.append({
            "action": "meet",
            "location": location,
            "person": friend,
            "start_time": minutes_to_time(start_time),
            "end_time": minutes_to_time(end_time)
        })
        
        current_time = end_time
        current_location = location
    
    # Output result as JSON
    result = {
        "itinerary": itinerary
    }
    
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()