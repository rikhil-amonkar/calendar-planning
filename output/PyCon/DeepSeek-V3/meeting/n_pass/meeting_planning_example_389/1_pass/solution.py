import constraint
from datetime import datetime, timedelta
import json

def main():
    # Travel times in minutes between locations
    travel_times = {
        ('Haight-Ashbury', 'Fisherman\'s Wharf'): 23,
        ('Haight-Ashbury', 'Richmond District'): 10,
        ('Haight-Ashbury', 'Mission District'): 11,
        ('Haight-Ashbury', 'Bayview'): 18,
        ('Fisherman\'s Wharf', 'Haight-Ashbury'): 22,
        ('Fisherman\'s Wharf', 'Richmond District'): 18,
        ('Fisherman\'s Wharf', 'Mission District'): 22,
        ('Fisherman\'s Wharf', 'Bayview'): 26,
        ('Richmond District', 'Haight-Ashbury'): 10,
        ('Richmond District', 'Fisherman\'s Wharf'): 18,
        ('Richmond District', 'Mission District'): 20,
        ('Richmond District', 'Bayview'): 26,
        ('Mission District', 'Haight-Ashbury'): 12,
        ('Mission District', 'Fisherman\'s Wharf'): 22,
        ('Mission District', 'Richmond District'): 20,
        ('Mission District', 'Bayview'): 15,
        ('Bayview', 'Haight-Ashbury'): 19,
        ('Bayview', 'Fisherman\'s Wharf'): 25,
        ('Bayview', 'Richmond District'): 25,
        ('Bayview', 'Mission District'): 13
    }
    
    # Friend availability (converted to minutes from 9:00)
    friend_availability = {
        'Sarah': {
            'location': 'Fisherman\'s Wharf',
            'start': (14, 45),  # 2:45 PM
            'end': (17, 30),    # 5:30 PM
            'min_duration': 105
        },
        'Mary': {
            'location': 'Richmond District', 
            'start': (13, 0),   # 1:00 PM
            'end': (19, 15),    # 7:15 PM
            'min_duration': 75
        },
        'Helen': {
            'location': 'Mission District',
            'start': (21, 45),  # 9:45 PM
            'end': (22, 30),    # 10:30 PM
            'min_duration': 30
        },
        'Thomas': {
            'location': 'Bayview',
            'start': (15, 15),  # 3:15 PM
            'end': (18, 45),    # 6:45 PM
            'min_duration': 120
        }
    }
    
    # Convert times to minutes from 9:00 (540 minutes)
    def time_to_minutes(hour, minute):
        return (hour * 60 + minute) - 540
    
    def minutes_to_time_str(minutes):
        total_minutes = 540 + minutes
        hours = total_minutes // 60
        mins = total_minutes % 60
        return f"{hours}:{mins:02d}"
    
    # Create problem
    problem = constraint.Problem()
    
    # Variables: start time and duration for each friend meeting
    friends = list(friend_availability.keys())
    
    for friend in friends:
        info = friend_availability[friend]
        start_min = time_to_minutes(*info['start'])
        end_min = time_to_minutes(*info['end'])
        min_dur = info['min_duration']
        
        # Start time can range from availability start to (end - min_duration)
        problem.addVariable(f"{friend}_start", range(start_min, end_min - min_dur + 1))
        # Duration must be at least min_duration
        problem.addVariable(f"{friend}_duration", range(min_dur, end_min - start_min + 1))
    
    # Add constraint that meetings don't overlap considering travel time
    def no_overlap(*args):
        # Extract all start times and durations
        values = {}
        for i, friend in enumerate(friends):
            values[f"{friend}_start"] = args[i * 2]
            values[f"{friend}_duration"] = args[i * 2 + 1]
        
        # Check all pairs of meetings
        for i, friend1 in enumerate(friends):
            for j, friend2 in enumerate(friends):
                if i >= j:
                    continue
                
                start1 = values[f"{friend1}_start"]
                end1 = start1 + values[f"{friend1}_duration"]
                start2 = values[f"{friend2}_start"]
                end2 = start2 + values[f"{friend2}_duration"]
                
                loc1 = friend_availability[friend1]['location']
                loc2 = friend_availability[friend2]['location']
                
                travel_time = travel_times.get((loc1, loc2), 0)
                
                # Check if meetings overlap considering travel time
                if (start1 < end2 + travel_time and end1 > start2 - travel_time):
                    return False
        
        return True
    
    # Add the no-overlap constraint
    all_vars = []
    for friend in friends:
        all_vars.append(f"{friend}_start")
        all_vars.append(f"{friend}_duration")
    
    problem.addConstraint(no_overlap, all_vars)
    
    # Objective: maximize total meeting time
    def objective(*args):
        total_duration = 0
        for i, friend in enumerate(friends):
            total_duration += args[i * 2 + 1]  # duration is at odd indices
        return total_duration
    
    # Find solution
    solutions = problem.getSolutions()
    
    if not solutions:
        # Fallback: try to meet as many friends as possible even if not all constraints can be satisfied
        best_solution = None
        best_score = -1
        
        for friend_count in range(len(friends), 0, -1):
            # Try to find solution with friend_count friends
            temp_problem = constraint.Problem()
            
            # Only add variables for a subset of friends
            for i, friend in enumerate(friends[:friend_count]):
                info = friend_availability[friend]
                start_min = time_to_minutes(*info['start'])
                end_min = time_to_minutes(*info['end'])
                min_dur = info['min_duration']
                
                temp_problem.addVariable(f"{friend}_start", range(start_min, end_min - min_dur + 1))
                temp_problem.addVariable(f"{friend}_duration", range(min_dur, end_min - start_min + 1))
            
            # Add no-overlap constraint for the subset
            subset_vars = []
            for friend in friends[:friend_count]:
                subset_vars.append(f"{friend}_start")
                subset_vars.append(f"{friend}_duration")
            
            temp_problem.addConstraint(no_overlap, subset_vars)
            
            temp_solutions = temp_problem.getSolutions()
            if temp_solutions:
                # Find solution with maximum total duration
                for sol in temp_solutions:
                    total_dur = sum(sol[f"{friend}_duration"] for friend in friends[:friend_count])
                    if total_dur > best_score:
                        best_score = total_dur
                        best_solution = sol
                break
        
        solution = best_solution
    else:
        # Find solution with maximum total duration
        best_solution = None
        best_score = -1
        for sol in solutions:
            total_dur = sum(sol[f"{friend}_duration"] for friend in friends)
            if total_dur > best_score:
                best_score = total_dur
                best_solution = sol
        solution = best_solution
    
    # Build itinerary
    itinerary = []
    if solution:
        # Create meeting events
        meetings = []
        for friend in friends:
            if f"{friend}_start" in solution:
                start_time = solution[f"{friend}_start"]
                duration = solution[f"{friend}_duration"]
                location = friend_availability[friend]['location']
                
                meetings.append({
                    'friend': friend,
                    'location': location,
                    'start': start_time,
                    'end': start_time + duration,
                    'duration': duration
                })
        
        # Sort meetings by start time
        meetings.sort(key=lambda x: x['start'])
        
        # Add travel from starting location (Haight-Ashbury) to first meeting
        current_location = 'Haight-Ashbury'
        
        for meeting in meetings:
            # Add travel time if needed
            if current_location != meeting['location']:
                travel_time = travel_times.get((current_location, meeting['location']), 0)
                # Ensure we arrive on time
                if meeting['start'] - travel_time < 0:
                    continue
            
            # Add meeting to itinerary
            itinerary.append({
                "action": "meet",
                "location": meeting['location'],
                "person": meeting['friend'],
                "start_time": minutes_to_time_str(meeting['start']),
                "end_time": minutes_to_time_str(meeting['end'])
            })
            
            current_location = meeting['location']
    
    # Output result
    result = {
        "itinerary": itinerary
    }
    
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()