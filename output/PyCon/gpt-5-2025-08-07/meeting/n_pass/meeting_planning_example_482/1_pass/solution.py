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
    # Travel times in minutes (symmetric matrix)
    travel_times = {
        'Haight-Ashbury': {
            'Mission District': 11,
            'Bayview': 18,
            'Pacific Heights': 12,
            'Russian Hill': 17,
            'Fisherman\'s Wharf': 23
        },
        'Mission District': {
            'Haight-Ashbury': 12,
            'Bayview': 15,
            'Pacific Heights': 16,
            'Russian Hill': 15,
            'Fisherman\'s Wharf': 22
        },
        'Bayview': {
            'Haight-Ashbury': 19,
            'Mission District': 13,
            'Pacific Heights': 23,
            'Russian Hill': 23,
            'Fisherman\'s Wharf': 25
        },
        'Pacific Heights': {
            'Haight-Ashbury': 11,
            'Mission District': 15,
            'Bayview': 22,
            'Russian Hill': 7,
            'Fisherman\'s Wharf': 13
        },
        'Russian Hill': {
            'Haight-Ashbury': 17,
            'Mission District': 16,
            'Bayview': 23,
            'Pacific Heights': 7,
            'Fisherman\'s Wharf': 7
        },
        'Fisherman\'s Wharf': {
            'Haight-Ashbury': 22,
            'Mission District': 22,
            'Bayview': 26,
            'Pacific Heights': 12,
            'Russian Hill': 7
        }
    }
    
    # Friend constraints
    friends = {
        'Stephanie': {
            'location': 'Mission District',
            'available_start': '8:15',
            'available_end': '13:45',
            'min_duration': 90
        },
        'Sandra': {
            'location': 'Bayview',
            'available_start': '13:00',
            'available_end': '19:30',
            'min_duration': 15
        },
        'Richard': {
            'location': 'Pacific Heights',
            'available_start': '7:15',
            'available_end': '10:15',
            'min_duration': 75
        },
        'Brian': {
            'location': 'Russian Hill',
            'available_start': '12:15',
            'available_end': '16:00',
            'min_duration': 120
        },
        'Jason': {
            'location': 'Fisherman\'s Wharf',
            'available_start': '8:30',
            'available_end': '17:45',
            'min_duration': 60
        }
    }
    
    # Convert all times to minutes
    start_location = 'Haight-Ashbury'
    current_time = time_to_minutes('9:00')
    
    # Create problem
    problem = constraint.Problem()
    
    # Define variables for each friend: (meet_order, start_time, duration)
    friend_names = list(friends.keys())
    
    # Add variables for whether we meet each friend (0 = don't meet, 1 = meet)
    for friend in friend_names:
        problem.addVariable(f'{friend}_meet', [0, 1])
    
    # Add variables for meeting order (0-4, -1 if not meeting)
    for friend in friend_names:
        problem.addVariable(f'{friend}_order', list(range(len(friend_names))) + [-1])
    
    # Add variables for start time and duration
    for friend in friend_names:
        info = friends[friend]
        available_start = time_to_minutes(info['available_start'])
        available_end = time_to_minutes(info['available_end'])
        min_duration = info['min_duration']
        
        # Possible start times (every 5 minutes within availability)
        start_times = list(range(available_start, available_end - min_duration + 1, 5))
        if not start_times:  # If no valid start times, add at least one
            start_times = [available_start]
        
        problem.addVariable(f'{friend}_start', start_times)
        problem.addVariable(f'{friend}_duration', list(range(min_duration, available_end - available_start + 1, 5)))
    
    # Constraints
    # 1. If not meeting, order is -1 and duration doesn't matter
    for friend in friend_names:
        problem.addConstraint(
            lambda meet, order, start, duration: 
                (meet == 1 and order != -1) or (meet == 0 and order == -1),
            [f'{friend}_meet', f'{friend}_order', f'{friend}_start', f'{friend}_duration']
        )
    
    # 2. All meeting orders must be unique (excluding -1)
    def unique_orders(*orders):
        meeting_orders = [o for o in orders if o != -1]
        return len(meeting_orders) == len(set(meeting_orders))
    
    problem.addConstraint(unique_orders, [f'{friend}_order' for friend in friend_names])
    
    # 3. Meeting must fit within availability window
    for friend in friend_names:
        info = friends[friend]
        available_start = time_to_minutes(info['available_start'])
        available_end = time_to_minutes(info['available_end'])
        
        def within_availability(meet, start, duration):
            if meet == 0:
                return True
            return start >= available_start and (start + duration) <= available_end
        
        problem.addConstraint(within_availability, 
                            [f'{friend}_meet', f'{friend}_start', f'{friend}_duration'])
    
    # 4. Travel time constraints between consecutive meetings
    def travel_constraint(*args):
        # Extract all variables
        meeting_data = {}
        for i, friend in enumerate(friend_names):
            meeting_data[friend] = {
                'meet': args[i*4],
                'order': args[i*4 + 1],
                'start': args[i*4 + 2],
                'duration': args[i*4 + 3]
            }
        
        # Get meetings in order
        meetings = [(friend, data) for friend, data in meeting_data.items() 
                   if data['meet'] == 1 and data['order'] != -1]
        meetings.sort(key=lambda x: x[1]['order'])
        
        current_loc = start_location
        current_time_val = current_time
        
        for i, (friend, data) in enumerate(meetings):
            friend_loc = friends[friend]['location']
            
            # Travel time to this location
            travel_time = travel_times[current_loc][friend_loc]
            
            # Arrival time at meeting
            arrival_time = current_time_val + travel_time
            
            # We must arrive before or at meeting start time
            if arrival_time > data['start']:
                return False
            
            # Update current location and time
            current_loc = friend_loc
            current_time_val = data['start'] + data['duration']
        
        return True
    
    # Create argument list for travel constraint
    travel_args = []
    for friend in friend_names:
        travel_args.extend([f'{friend}_meet', f'{friend}_order', f'{friend}_start', f'{friend}_duration'])
    
    problem.addConstraint(travel_constraint, travel_args)
    
    # Objective: maximize number of meetings and total meeting time
    def objective(*args):
        total_meetings = 0
        total_duration = 0
        
        for i, friend in enumerate(friend_names):
            meet = args[i*4]
            duration = args[i*4 + 3]
            
            if meet == 1:
                total_meetings += 1
                total_duration += duration
        
        # Prioritize number of meetings, then total duration
        return total_meetings * 1000 + total_duration
    
    # Find solution
    solutions = problem.getSolutions()
    
    if not solutions:
        # Fallback: try to meet at least some friends
        # Relax constraints and try again
        best_solution = None
        best_score = -1
        
        for friend in friend_names:
            # Try meeting just this one friend
            test_problem = constraint.Problem()
            
            # Only allow this friend to be met
            for f in friend_names:
                if f == friend:
                    test_problem.addVariable(f'{f}_meet', [1])
                    test_problem.addVariable(f'{f}_order', [0])
                else:
                    test_problem.addVariable(f'{f}_meet', [0])
                    test_problem.addVariable(f'{f}_order', [-1])
            
            # Add other variables and constraints
            for f in friend_names:
                info = friends[f]
                available_start = time_to_minutes(info['available_start'])
                available_end = time_to_minutes(info['available_end'])
                min_duration = info['min_duration']
                
                start_times = list(range(available_start, available_end - min_duration + 1, 5))
                if not start_times:
                    start_times = [available_start]
                
                test_problem.addVariable(f'{f}_start', start_times)
                test_problem.addVariable(f'{f}_duration', 
                                       list(range(min_duration, available_end - available_start + 1, 5)))
            
            # Add travel constraint
            travel_args = []
            for f in friend_names:
                travel_args.extend([f'{f}_meet', f'{f}_order', f'{f}_start', f'{f}_duration'])
            
            test_problem.addConstraint(travel_constraint, travel_args)
            
            test_solutions = test_problem.getSolutions()
            if test_solutions:
                score = objective(*[test_solutions[0][arg] for arg in travel_args])
                if score > best_score:
                    best_score = score
                    best_solution = test_solutions[0]
        
        if best_solution:
            solution = best_solution
        else:
            # Last resort: empty itinerary
            solution = {}
            for friend in friend_names:
                solution[f'{friend}_meet'] = 0
                solution[f'{friend}_order'] = -1
                solution[f'{friend}_start'] = time_to_minutes(friends[friend]['available_start'])
                solution[f'{friend}_duration'] = friends[friend]['min_duration']
    else:
        # Find best solution
        best_solution = None
        best_score = -1
        
        for sol in solutions:
            score = objective(*[sol[arg] for arg in travel_args])
            if score > best_score:
                best_score = score
                best_solution = sol
        
        solution = best_solution
    
    # Build itinerary
    itinerary = []
    
    # Collect meetings that actually happened
    meetings = []
    for friend in friend_names:
        if solution.get(f'{friend}_meet', 0) == 1 and solution.get(f'{friend}_order', -1) != -1:
            meetings.append({
                'friend': friend,
                'location': friends[friend]['location'],
                'order': solution[f'{friend}_order'],
                'start': solution[f'{friend}_start'],
                'duration': solution[f'{friend}_duration']
            })
    
    # Sort by order
    meetings.sort(key=lambda x: x['order'])
    
    # Add travel from start location to first meeting
    if meetings:
        first_meeting = meetings[0]
        travel_time = travel_times[start_location][first_meeting['location']]
        travel_start = current_time
        travel_end = current_time + travel_time
        
        itinerary.append({
            "action": "travel",
            "location": first_meeting['location'],
            "person": "",
            "start_time": minutes_to_time(travel_start),
            "end_time": minutes_to_time(travel_end)
        })
    
    # Add meetings and travel between them
    for i, meeting in enumerate(meetings):
        # Add meeting
        itinerary.append({
            "action": "meet",
            "location": meeting['location'],
            "person": meeting['friend'],
            "start_time": minutes_to_time(meeting['start']),
            "end_time": minutes_to_time(meeting['start'] + meeting['duration'])
        })
        
        # Add travel to next meeting if there is one
        if i < len(meetings) - 1:
            next_meeting = meetings[i + 1]
            travel_time = travel_times[meeting['location']][next_meeting['location']]
            travel_start = meeting['start'] + meeting['duration']
            travel_end = travel_start + travel_time
            
            itinerary.append({
                "action": "travel",
                "location": next_meeting['location'],
                "person": "",
                "start_time": minutes_to_time(travel_start),
                "end_time": minutes_to_time(travel_end)
            })
    
    # Output result
    result = {
        "itinerary": itinerary
    }
    
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()