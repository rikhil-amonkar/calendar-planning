import constraint
from datetime import datetime, timedelta
import json

def main():
    # Travel times in minutes between locations
    travel_times = {
        ('Bayview', 'North Beach'): 21,
        ('Bayview', 'Presidio'): 31,
        ('Bayview', 'Haight-Ashbury'): 19,
        ('Bayview', 'Union Square'): 17,
        ('North Beach', 'Bayview'): 22,
        ('North Beach', 'Presidio'): 17,
        ('North Beach', 'Haight-Ashbury'): 18,
        ('North Beach', 'Union Square'): 7,
        ('Presidio', 'Bayview'): 31,
        ('Presidio', 'North Beach'): 18,
        ('Presidio', 'Haight-Ashbury'): 15,
        ('Presidio', 'Union Square'): 22,
        ('Haight-Ashbury', 'Bayview'): 18,
        ('Haight-Ashbury', 'North Beach'): 19,
        ('Haight-Ashbury', 'Presidio'): 15,
        ('Haight-Ashbury', 'Union Square'): 17,
        ('Union Square', 'Bayview'): 15,
        ('Union Square', 'North Beach'): 10,
        ('Union Square', 'Presidio'): 24,
        ('Union Square', 'Haight-Ashbury'): 18
    }
    
    # Convert times to minutes since 9:00 AM
    def time_to_minutes(time_str):
        time_obj = datetime.strptime(time_str, '%I:%M%p')
        base_time = datetime.strptime('9:00AM', '%I:%M%p')
        delta = time_obj - base_time
        return int(delta.total_seconds() / 60)
    
    # Convert minutes since 9:00 AM back to time string
    def minutes_to_time(minutes):
        base_time = datetime.strptime('9:00AM', '%I:%M%p')
        result_time = base_time + timedelta(minutes=minutes)
        return result_time.strftime('%H:%M').lstrip('0')
    
    # Friend constraints
    friends = {
        'Barbara': {
            'location': 'North Beach',
            'available_start': time_to_minutes('1:45PM'),
            'available_end': time_to_minutes('8:15PM'),
            'min_duration': 60
        },
        'Margaret': {
            'location': 'Presidio',
            'available_start': time_to_minutes('10:15AM'),
            'available_end': time_to_minutes('3:15PM'),
            'min_duration': 30
        },
        'Kevin': {
            'location': 'Haight-Ashbury',
            'available_start': time_to_minutes('8:00PM'),
            'available_end': time_to_minutes('8:45PM'),
            'min_duration': 30
        },
        'Kimberly': {
            'location': 'Union Square',
            'available_start': time_to_minutes('7:45AM'),
            'available_end': time_to_minutes('4:45PM'),
            'min_duration': 30
        }
    }
    
    friend_names = list(friends.keys())
    
    problem = constraint.Problem()
    
    # Variables: start time for each meeting
    for friend in friend_names:
        friend_info = friends[friend]
        earliest_start = friend_info['available_start']
        latest_start = friend_info['available_end'] - friend_info['min_duration']
        problem.addVariable(f"{friend}_start", range(earliest_start, latest_start + 1))
        problem.addVariable(f"{friend}_duration", [friend_info['min_duration']])
    
    # Add variable for meeting order
    problem.addVariable("order", range(24))  # Simple ordering variable
    
    # Constraints
    def all_meetings_valid(*args):
        # Extract start times and durations
        starts = {}
        durations = {}
        for i, friend in enumerate(friend_names):
            starts[friend] = args[i]
            durations[friend] = args[i + len(friend_names)]
        
        # Check if all meetings fit within availability windows
        for friend in friend_names:
            friend_info = friends[friend]
            start = starts[friend]
            duration = durations[friend]
            end = start + duration
            
            if start < friend_info['available_start'] or end > friend_info['available_end']:
                return False
        
        # Create ordered list of meetings
        meetings = [(friend, starts[friend], durations[friend], friends[friend]['location']) for friend in friend_names]
        meetings.sort(key=lambda x: x[1])  # Sort by start time
        
        # Check travel times between consecutive meetings
        for i in range(len(meetings) - 1):
            current_friend, current_start, current_duration, current_loc = meetings[i]
            next_friend, next_start, next_duration, next_loc = meetings[i + 1]
            
            current_end = current_start + current_duration
            travel_time = travel_times.get((current_loc, next_loc), 999)
            
            if current_end + travel_time > next_start:
                return False
        
        return True
    
    # Add the constraint
    all_vars = []
    for friend in friend_names:
        all_vars.append(f"{friend}_start")
    for friend in friend_names:
        all_vars.append(f"{friend}_duration")
    all_vars.append("order")
    
    problem.addConstraint(all_meetings_valid, all_vars)
    
    # Find solutions
    solutions = problem.getSolutions()
    
    if not solutions:
        # Fallback: try to meet as many friends as possible
        best_solution = None
        max_meetings = 0
        
        # Try all subsets of friends
        from itertools import combinations
        for subset_size in range(len(friend_names), 0, -1):
            for subset in combinations(friend_names, subset_size):
                sub_problem = constraint.Problem()
                
                for friend in subset:
                    friend_info = friends[friend]
                    earliest_start = friend_info['available_start']
                    latest_start = friend_info['available_end'] - friend_info['min_duration']
                    sub_problem.addVariable(f"{friend}_start", range(earliest_start, latest_start + 1))
                    sub_problem.addVariable(f"{friend}_duration", [friend_info['min_duration']])
                
                sub_problem.addVariable("order", range(24))
                
                def subset_valid(*args):
                    starts = {}
                    durations = {}
                    for i, friend in enumerate(subset):
                        starts[friend] = args[i]
                        durations[friend] = args[i + len(subset)]
                    
                    for friend in subset:
                        friend_info = friends[friend]
                        start = starts[friend]
                        duration = durations[friend]
                        end = start + duration
                        
                        if start < friend_info['available_start'] or end > friend_info['available_end']:
                            return False
                    
                    meetings = [(friend, starts[friend], durations[friend], friends[friend]['location']) for friend in subset]
                    meetings.sort(key=lambda x: x[1])
                    
                    for i in range(len(meetings) - 1):
                        current_friend, current_start, current_duration, current_loc = meetings[i]
                        next_friend, next_start, next_duration, next_loc = meetings[i + 1]
                        
                        current_end = current_start + current_duration
                        travel_time = travel_times.get((current_loc, next_loc), 999)
                        
                        if current_end + travel_time > next_start:
                            return False
                    
                    return True
                
                sub_vars = []
                for friend in subset:
                    sub_vars.append(f"{friend}_start")
                for friend in subset:
                    sub_vars.append(f"{friend}_duration")
                sub_vars.append("order")
                
                sub_problem.addConstraint(subset_valid, sub_vars)
                sub_solutions = sub_problem.getSolutions()
                
                if sub_solutions:
                    best_solution = sub_solutions[0]
                    max_meetings = subset_size
                    break
            
            if best_solution:
                break
        
        if best_solution:
            solution = best_solution
            used_friends = subset if 'subset' in locals() else friend_names
        else:
            # If no solution found, return empty itinerary
            print(json.dumps({"itinerary": []}, indent=2))
            return
    else:
        solution = solutions[0]
        used_friends = friend_names
    
    # Build itinerary
    itinerary = []
    meetings = []
    
    for friend in used_friends:
        start_time = solution[f"{friend}_start"]
        duration = solution[f"{friend}_duration"]
        location = friends[friend]['location']
        meetings.append((friend, start_time, duration, location))
    
    # Sort meetings by start time
    meetings.sort(key=lambda x: x[1])
    
    # Add travel from starting location (Bayview) to first meeting
    current_location = 'Bayview'
    for friend, start_time, duration, location in meetings:
        # Add travel if needed
        if current_location != location:
            travel_time = travel_times.get((current_location, location), 0)
        
        # Add meeting
        itinerary.append({
            "action": "meet",
            "location": location,
            "person": friend,
            "start_time": minutes_to_time(start_time),
            "end_time": minutes_to_time(start_time + duration)
        })
        
        current_location = location
    
    # Output result
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()