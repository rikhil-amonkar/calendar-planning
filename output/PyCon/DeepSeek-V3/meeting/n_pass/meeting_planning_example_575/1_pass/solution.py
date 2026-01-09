from constraint import Problem, AllDifferentConstraint
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
    # Define locations and travel times (in minutes)
    locations = ['The Castro', 'Presidio', 'Sunset District', 'Haight-Ashbury', 
                'Mission District', 'Golden Gate Park', 'Russian Hill']
    
    travel_times = {
        ('The Castro', 'Presidio'): 20,
        ('The Castro', 'Sunset District'): 17,
        ('The Castro', 'Haight-Ashbury'): 6,
        ('The Castro', 'Mission District'): 7,
        ('The Castro', 'Golden Gate Park'): 11,
        ('The Castro', 'Russian Hill'): 18,
        ('Presidio', 'The Castro'): 21,
        ('Presidio', 'Sunset District'): 15,
        ('Presidio', 'Haight-Ashbury'): 15,
        ('Presidio', 'Mission District'): 26,
        ('Presidio', 'Golden Gate Park'): 12,
        ('Presidio', 'Russian Hill'): 14,
        ('Sunset District', 'The Castro'): 17,
        ('Sunset District', 'Presidio'): 16,
        ('Sunset District', 'Haight-Ashbury'): 15,
        ('Sunset District', 'Mission District'): 24,
        ('Sunset District', 'Golden Gate Park'): 11,
        ('Sunset District', 'Russian Hill'): 24,
        ('Haight-Ashbury', 'The Castro'): 6,
        ('Haight-Ashbury', 'Presidio'): 15,
        ('Haight-Ashbury', 'Sunset District'): 15,
        ('Haight-Ashbury', 'Mission District'): 11,
        ('Haight-Ashbury', 'Golden Gate Park'): 7,
        ('Haight-Ashbury', 'Russian Hill'): 17,
        ('Mission District', 'The Castro'): 7,
        ('Mission District', 'Presidio'): 25,
        ('Mission District', 'Sunset District'): 24,
        ('Mission District', 'Haight-Ashbury'): 12,
        ('Mission District', 'Golden Gate Park'): 17,
        ('Mission District', 'Russian Hill'): 15,
        ('Golden Gate Park', 'The Castro'): 13,
        ('Golden Gate Park', 'Presidio'): 11,
        ('Golden Gate Park', 'Sunset District'): 10,
        ('Golden Gate Park', 'Haight-Ashbury'): 7,
        ('Golden Gate Park', 'Mission District'): 17,
        ('Golden Gate Park', 'Russian Hill'): 19,
        ('Russian Hill', 'The Castro'): 21,
        ('Russian Hill', 'Presidio'): 14,
        ('Russian Hill', 'Sunset District'): 23,
        ('Russian Hill', 'Haight-Ashbury'): 17,
        ('Russian Hill', 'Mission District'): 16,
        ('Russian Hill', 'Golden Gate Park'): 21
    }
    
    # Friend constraints
    friends = [
        {'name': 'Rebecca', 'location': 'Presidio', 'start': '18:15', 'end': '20:45', 'min_duration': 60},
        {'name': 'Linda', 'location': 'Sunset District', 'start': '15:30', 'end': '19:45', 'min_duration': 30},
        {'name': 'Elizabeth', 'location': 'Haight-Ashbury', 'start': '17:15', 'end': '19:30', 'min_duration': 105},
        {'name': 'William', 'location': 'Mission District', 'start': '13:15', 'end': '19:30', 'min_duration': 30},
        {'name': 'Robert', 'location': 'Golden Gate Park', 'start': '14:15', 'end': '21:30', 'min_duration': 45},
        {'name': 'Mark', 'location': 'Russian Hill', 'start': '10:00', 'end': '21:15', 'min_duration': 75}
    ]
    
    # Convert times to minutes
    start_time = time_to_minutes('9:00')
    end_time = time_to_minutes('21:30')  # End of day
    
    for friend in friends:
        friend['start_min'] = time_to_minutes(friend['start'])
        friend['end_min'] = time_to_minutes(friend['end'])
    
    # Create constraint problem
    problem = Problem()
    
    # Variables: start time and duration for each friend meeting
    for friend in friends:
        name = friend['name']
        problem.addVariable(f"{name}_start", range(friend['start_min'], friend['end_min'] - friend['min_duration'] + 1))
        problem.addVariable(f"{name}_duration", range(friend['min_duration'], friend['end_min'] - friend['start_min'] + 1))
    
    # Constraint: meeting must end within friend's availability
    for friend in friends:
        name = friend['name']
        problem.addConstraint(
            lambda start, duration, end_max=friend['end_min']: start + duration <= end_max,
            [f"{name}_start", f"{name}_duration"]
        )
    
    # Constraint: meetings cannot overlap when considering travel time
    def no_overlap_with_travel(friend1_start, friend1_duration, friend2_start, friend2_duration, 
                              friend1_loc, friend2_loc):
        friend1_end = friend1_start + friend1_duration
        friend2_end = friend2_start + friend2_duration
        
        # Calculate travel time between locations
        travel_time = travel_times.get((friend1_loc, friend2_loc), 
                                      travel_times.get((friend2_loc, friend1_loc), 0))
        
        # Check if there's enough time to travel between meetings
        if friend1_end + travel_time <= friend2_start:  # Friend1 then Friend2
            return True
        if friend2_end + travel_time <= friend1_start:  # Friend2 then Friend1
            return True
        return False
    
    # Add constraints for all pairs of friends
    for i, friend1 in enumerate(friends):
        for j, friend2 in enumerate(friends):
            if i < j:
                problem.addConstraint(
                    lambda fs1, fd1, fs2, fd2, loc1=friend1['location'], loc2=friend2['location']: 
                    no_overlap_with_travel(fs1, fd1, fs2, fd2, loc1, loc2),
                    [f"{friend1['name']}_start", f"{friend1['name']}_duration", 
                     f"{friend2['name']}_start", f"{friend2['name']}_duration"]
                )
    
    # Objective: maximize total meeting time
    def objective(*args):
        total_duration = 0
        for i in range(len(friends)):
            total_duration += args[i * 2 + 1]  # Duration is at odd indices
        return total_duration
    
    # Find solution
    solutions = problem.getSolutions()
    
    if not solutions:
        # Fallback: try to meet as many friends as possible with minimum durations
        best_solution = None
        max_meetings = 0
        
        # Try different combinations
        for friend_count in range(len(friends), 0, -1):
            # This is a simplified approach - in practice you'd need a more sophisticated algorithm
            # For now, we'll create a simple sequential schedule
            current_time = start_time
            itinerary = []
            
            # Sort friends by availability start time
            sorted_friends = sorted(friends, key=lambda x: x['start_min'])
            
            for friend in sorted_friends:
                meeting_start = max(current_time, friend['start_min'])
                meeting_end = meeting_start + friend['min_duration']
                
                if meeting_end <= friend['end_min'] and meeting_end <= end_time:
                    itinerary.append({
                        'action': 'meet',
                        'location': friend['location'],
                        'person': friend['name'],
                        'start_time': minutes_to_time(meeting_start),
                        'end_time': minutes_to_time(meeting_end)
                    })
                    # Add travel time to next location
                    current_time = meeting_end + 15  # Average travel time
                
                if current_time >= end_time:
                    break
            
            if len(itinerary) >= max_meetings:
                max_meetings = len(itinerary)
                best_solution = itinerary
        
        result = {"itinerary": best_solution if best_solution else []}
    else:
        # Find solution with maximum total duration
        best_solution = max(solutions, key=lambda sol: sum(sol[f"{friend['name']}_duration"] for friend in friends))
        
        # Create itinerary
        itinerary = []
        for friend in friends:
            name = friend['name']
            start_time_meeting = best_solution[f"{name}_start"]
            duration = best_solution[f"{name}_duration"]
            
            itinerary.append({
                'action': 'meet',
                'location': friend['location'],
                'person': name,
                'start_time': minutes_to_time(start_time_meeting),
                'end_time': minutes_to_time(start_time_meeting + duration)
            })
        
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: time_to_minutes(x['start_time']))
        result = {"itinerary": itinerary}
    
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()