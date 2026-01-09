import constraint
from datetime import datetime, timedelta
import json

def main():
    # Define locations
    locations = ['Bayview', 'Nob Hill', 'Union Square', 'Chinatown', 'The Castro', 'Presidio', 'Pacific Heights', 'Russian Hill']
    
    # Travel times matrix (in minutes)
    travel_times = {
        'Bayview': {'Bayview': 0, 'Nob Hill': 20, 'Union Square': 17, 'Chinatown': 18, 'The Castro': 20, 'Presidio': 31, 'Pacific Heights': 23, 'Russian Hill': 23},
        'Nob Hill': {'Bayview': 19, 'Nob Hill': 0, 'Union Square': 7, 'Chinatown': 6, 'The Castro': 17, 'Presidio': 17, 'Pacific Heights': 8, 'Russian Hill': 5},
        'Union Square': {'Bayview': 15, 'Nob Hill': 9, 'Union Square': 0, 'Chinatown': 7, 'The Castro': 19, 'Presidio': 24, 'Pacific Heights': 15, 'Russian Hill': 13},
        'Chinatown': {'Bayview': 22, 'Nob Hill': 8, 'Union Square': 7, 'Chinatown': 0, 'The Castro': 22, 'Presidio': 19, 'Pacific Heights': 10, 'Russian Hill': 7},
        'The Castro': {'Bayview': 19, 'Nob Hill': 16, 'Union Square': 19, 'Chinatown': 20, 'The Castro': 0, 'Presidio': 20, 'Pacific Heights': 16, 'Russian Hill': 18},
        'Presidio': {'Bayview': 31, 'Nob Hill': 18, 'Union Square': 22, 'Chinatown': 21, 'The Castro': 21, 'Presidio': 0, 'Pacific Heights': 11, 'Russian Hill': 14},
        'Pacific Heights': {'Bayview': 22, 'Nob Hill': 8, 'Union Square': 12, 'Chinatown': 11, 'The Castro': 16, 'Presidio': 11, 'Pacific Heights': 0, 'Russian Hill': 7},
        'Russian Hill': {'Bayview': 23, 'Nob Hill': 5, 'Union Square': 11, 'Chinatown': 9, 'The Castro': 21, 'Presidio': 14, 'Pacific Heights': 7, 'Russian Hill': 0}
    }
    
    # Friend constraints
    friends = [
        {'name': 'Paul', 'location': 'Nob Hill', 'available_start': '16:15', 'available_end': '21:15', 'min_duration': 60},
        {'name': 'Carol', 'location': 'Union Square', 'available_start': '18:00', 'available_end': '20:15', 'min_duration': 120},
        {'name': 'Patricia', 'location': 'Chinatown', 'available_start': '20:00', 'available_end': '21:30', 'min_duration': 75},
        {'name': 'Karen', 'location': 'The Castro', 'available_start': '17:00', 'available_end': '19:00', 'min_duration': 45},
        {'name': 'Nancy', 'location': 'Presidio', 'available_start': '11:45', 'available_end': '22:00', 'min_duration': 30},
        {'name': 'Jeffrey', 'location': 'Pacific Heights', 'available_start': '20:00', 'available_end': '20:45', 'min_duration': 45},
        {'name': 'Matthew', 'location': 'Russian Hill', 'available_start': '15:45', 'available_end': '21:45', 'min_duration': 75}
    ]
    
    # Convert time strings to minutes since 9:00
    def time_to_minutes(time_str):
        if ':' in time_str:
            hours, minutes = map(int, time_str.split(':'))
            return (hours - 9) * 60 + minutes
        return 0
    
    def minutes_to_time(minutes):
        total_hours = 9 + minutes // 60
        total_minutes = minutes % 60
        return f"{total_hours}:{total_minutes:02d}"
    
    # Create problem
    problem = constraint.Problem()
    
    # Variables: start time and duration for each friend
    for i, friend in enumerate(friends):
        available_start = time_to_minutes(friend['available_start'])
        available_end = time_to_minutes(friend['available_end'])
        min_duration = friend['min_duration']
        
        # Start time must be within availability window
        problem.addVariable(f'start_{i}', range(available_start, available_end - min_duration + 1))
        # Duration must be at least the minimum
        problem.addVariable(f'duration_{i}', range(min_duration, available_end - available_start + 1))
    
    # Add constraint: meetings cannot overlap and must account for travel time
    def no_overlap(*args):
        # Extract all start times and durations
        starts = [args[i] for i in range(0, len(args), 2)]
        durations = [args[i] for i in range(1, len(args), 2)]
        
        # Create meeting intervals
        meetings = []
        for i in range(len(friends)):
            meetings.append({
                'start': starts[i],
                'end': starts[i] + durations[i],
                'location': friends[i]['location'],
                'index': i
            })
        
        # Sort by start time
        meetings.sort(key=lambda x: x['start'])
        
        # Check for overlaps considering travel time
        for j in range(1, len(meetings)):
            prev_meeting = meetings[j-1]
            curr_meeting = meetings[j]
            
            travel_time = travel_times[prev_meeting['location']][curr_meeting['location']]
            
            if prev_meeting['end'] + travel_time > curr_meeting['start']:
                return False
        
        return True
    
    # Add the no-overlap constraint
    all_vars = []
    for i in range(len(friends)):
        all_vars.append(f'start_{i}')
        all_vars.append(f'duration_{i}')
    
    problem.addConstraint(no_overlap, all_vars)
    
    # Objective: maximize total meeting time
    def objective(*args):
        durations = [args[i] for i in range(1, len(args), 2)]
        return sum(durations)
    
    # Find solution
    solutions = problem.getSolutions()
    
    if not solutions:
        # Fallback: try to meet as many friends as possible with minimum duration
        best_solution = None
        best_score = -1
        
        for friend_count in range(len(friends), 0, -1):
            # Reset problem
            problem = constraint.Problem()
            
            # Add variables for subset of friends
            for i in range(friend_count):
                friend = friends[i]
                available_start = time_to_minutes(friend['available_start'])
                available_end = time_to_minutes(friend['available_end'])
                min_duration = friend['min_duration']
                
                problem.addVariable(f'start_{i}', range(available_start, available_end - min_duration + 1))
                problem.addVariable(f'duration_{i}', [min_duration])  # Only minimum duration
            
            # Add no-overlap constraint
            all_vars = []
            for i in range(friend_count):
                all_vars.append(f'start_{i}')
                all_vars.append(f'duration_{i}')
            
            problem.addConstraint(no_overlap, all_vars)
            
            solutions = problem.getSolutions()
            if solutions:
                best_solution = solutions[0]
                best_score = friend_count
                break
        
        if best_solution is None:
            # If still no solution, create a minimal itinerary
            itinerary = []
            current_time = time_to_minutes('9:00')
            
            for friend in friends:
                available_start = time_to_minutes(friend['available_start'])
                available_end = time_to_minutes(friend['available_end'])
                min_duration = friend['min_duration']
                
                # Check if we can meet this friend
                arrival_time = current_time + travel_times['Bayview' if not itinerary else itinerary[-1]['location']][friend['location']]
                start_time = max(arrival_time, available_start)
                
                if start_time + min_duration <= available_end:
                    itinerary.append({
                        'action': 'meet',
                        'location': friend['location'],
                        'person': friend['name'],
                        'start_time': minutes_to_time(start_time),
                        'end_time': minutes_to_time(start_time + min_duration)
                    })
                    current_time = start_time + min_duration
            
            result = {'itinerary': itinerary}
            print(json.dumps(result, indent=2))
            return
        
        solution = best_solution
    else:
        # Find solution with maximum total meeting time
        best_solution = None
        best_score = -1
        
        for sol in solutions:
            score = sum(sol[f'duration_{i}'] for i in range(len(friends)))
            if score > best_score:
                best_score = score
                best_solution = sol
        
        solution = best_solution
    
    # Build itinerary
    meetings = []
    for i in range(len(friends)):
        if f'start_{i}' in solution:
            start_time = solution[f'start_{i}']
            duration = solution[f'duration_{i}']
            friend = friends[i]
            
            meetings.append({
                'start': start_time,
                'end': start_time + duration,
                'location': friend['location'],
                'person': friend['name']
            })
    
    # Sort meetings by start time
    meetings.sort(key=lambda x: x['start'])
    
    # Add travel from starting point
    itinerary = []
    current_location = 'Bayview'
    current_time = time_to_minutes('9:00')
    
    for meeting in meetings:
        # Add travel time
        travel_time = travel_times[current_location][meeting['location']]
        arrival_time = current_time + travel_time
        
        # Ensure we don't start before available time
        actual_start = max(arrival_time, meeting['start'])
        
        itinerary.append({
            'action': 'meet',
            'location': meeting['location'],
            'person': meeting['person'],
            'start_time': minutes_to_time(actual_start),
            'end_time': minutes_to_time(meeting['end'])
        })
        
        current_location = meeting['location']
        current_time = meeting['end']
    
    result = {'itinerary': itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()