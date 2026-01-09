import constraint
from datetime import datetime, timedelta
import json

def main():
    # Travel times in minutes
    travel_times = {
        ('Sunset District', 'Alamo Square'): 17,
        ('Sunset District', 'Russian Hill'): 24,
        ('Sunset District', 'Golden Gate Park'): 11,
        ('Sunset District', 'Mission District'): 24,
        ('Alamo Square', 'Sunset District'): 16,
        ('Alamo Square', 'Russian Hill'): 13,
        ('Alamo Square', 'Golden Gate Park'): 9,
        ('Alamo Square', 'Mission District'): 10,
        ('Russian Hill', 'Sunset District'): 23,
        ('Russian Hill', 'Alamo Square'): 15,
        ('Russian Hill', 'Golden Gate Park'): 21,
        ('Russian Hill', 'Mission District'): 16,
        ('Golden Gate Park', 'Sunset District'): 10,
        ('Golden Gate Park', 'Alamo Square'): 10,
        ('Golden Gate Park', 'Russian Hill'): 19,
        ('Golden Gate Park', 'Mission District'): 17,
        ('Mission District', 'Sunset District'): 24,
        ('Mission District', 'Alamo Square'): 11,
        ('Mission District', 'Russian Hill'): 15,
        ('Mission District', 'Golden Gate Park'): 17
    }
    
    # Convert all times to minutes since 9:00 AM (540 minutes)
    start_time_minutes = 540  # 9:00 AM
    
    # Friend constraints in minutes since midnight
    friend_constraints = {
        'Charles': {
            'location': 'Alamo Square',
            'available_start': 1080,  # 6:00 PM (18:00)
            'available_end': 1305,    # 8:45 PM (20:45)
            'min_duration': 90
        },
        'Margaret': {
            'location': 'Russian Hill',
            'available_start': 540,   # 9:00 AM
            'available_end': 960,     # 4:00 PM (16:00)
            'min_duration': 30
        },
        'Daniel': {
            'location': 'Golden Gate Park',
            'available_start': 480,   # 8:00 AM
            'available_end': 810,     # 1:30 PM (13:30)
            'min_duration': 15
        },
        'Stephanie': {
            'location': 'Mission District',
            'available_start': 1230,  # 8:30 PM (20:30)
            'available_end': 1320,    # 10:00 PM (22:00)
            'min_duration': 90
        }
    }
    
    friends = list(friend_constraints.keys())
    
    problem = constraint.Problem()
    
    # Variables: start time and duration for each friend
    for friend in friends:
        constraints = friend_constraints[friend]
        min_start = constraints['available_start']
        max_start = constraints['available_end'] - constraints['min_duration']
        problem.addVariable(f"{friend}_start", range(min_start, max_start + 1))
        problem.addVariable(f"{friend}_duration", [constraints['min_duration']])
    
    # Constraint: meetings cannot overlap and must account for travel
    def no_overlap_and_travel(*args):
        # Parse all start times and durations
        schedules = {}
        for i, friend in enumerate(friends):
            start = args[i * 2]
            duration = args[i * 2 + 1]
            schedules[friend] = {
                'start': start,
                'end': start + duration,
                'location': friend_constraints[friend]['location']
            }
        
        # Create ordered list of meetings by start time
        ordered_meetings = sorted(schedules.items(), key=lambda x: x[1]['start'])
        
        # Check for overlaps and travel time
        for i in range(len(ordered_meetings) - 1):
            current_friend, current = ordered_meetings[i]
            next_friend, next_meeting = ordered_meetings[i + 1]
            
            travel_time = travel_times.get(
                (current['location'], next_meeting['location']), 0
            )
            
            # Current meeting end + travel time must be <= next meeting start
            if current['end'] + travel_time > next_meeting['start']:
                return False
        
        return True
    
    # Add constraint for all combinations
    all_vars = []
    for friend in friends:
        all_vars.append(f"{friend}_start")
        all_vars.append(f"{friend}_duration")
    
    problem.addConstraint(no_overlap_and_travel, all_vars)
    
    # Find solutions
    solutions = problem.getSolutions()
    
    if not solutions:
        # Fallback: try to maximize number of meetings with relaxed constraints
        best_solution = None
        max_meetings = 0
        
        # Try all subsets of friends
        from itertools import combinations
        for r in range(len(friends), 0, -1):
            for friend_subset in combinations(friends, r):
                sub_problem = constraint.Problem()
                
                for friend in friend_subset:
                    constraints = friend_constraints[friend]
                    min_start = constraints['available_start']
                    max_start = constraints['available_end'] - constraints['min_duration']
                    sub_problem.addVariable(f"{friend}_start", range(min_start, max_start + 1))
                    sub_problem.addVariable(f"{friend}_duration", [constraints['min_duration']])
                
                sub_vars = []
                for friend in friend_subset:
                    sub_vars.append(f"{friend}_start")
                    sub_vars.append(f"{friend}_duration")
                
                sub_problem.addConstraint(no_overlap_and_travel, sub_vars)
                sub_solutions = sub_problem.getSolutions()
                
                if sub_solutions:
                    best_solution = sub_solutions[0]
                    max_meetings = r
                    break
            
            if best_solution:
                break
        
        if not best_solution:
            # If still no solution, create empty itinerary
            result = {"itinerary": []}
            print(json.dumps(result, indent=2))
            return
        
        solution = best_solution
    else:
        solution = solutions[0]
    
    # Build itinerary
    itinerary = []
    current_location = 'Sunset District'
    current_time = start_time_minutes
    
    # Create list of meetings with their details
    meetings = []
    for friend in friends:
        if f"{friend}_start" in solution:
            start_time = solution[f"{friend}_start"]
            duration = solution[f"{friend}_duration"]
            location = friend_constraints[friend]['location']
            meetings.append({
                'friend': friend,
                'location': location,
                'start': start_time,
                'end': start_time + duration,
                'duration': duration
            })
    
    # Sort meetings by start time
    meetings.sort(key=lambda x: x['start'])
    
    # Add travel to first meeting if needed
    if meetings:
        first_meeting = meetings[0]
        travel_time = travel_times.get((current_location, first_meeting['location']), 0)
        
        # Only add travel if we're not already at the location
        if current_location != first_meeting['location'] and current_time + travel_time <= first_meeting['start']:
            itinerary.append({
                "action": "travel",
                "location": first_meeting['location'],
                "person": "",
                "start_time": minutes_to_time(current_time),
                "end_time": minutes_to_time(current_time + travel_time)
            })
            current_time += travel_time
            current_location = first_meeting['location']
    
    # Add meetings and travel between them
    for i, meeting in enumerate(meetings):
        # Add the meeting
        itinerary.append({
            "action": "meet",
            "location": meeting['location'],
            "person": meeting['friend'],
            "start_time": minutes_to_time(meeting['start']),
            "end_time": minutes_to_time(meeting['end'])
        })
        
        current_time = meeting['end']
        current_location = meeting['location']
        
        # Add travel to next meeting if there is one
        if i < len(meetings) - 1:
            next_meeting = meetings[i + 1]
            travel_time = travel_times.get((current_location, next_meeting['location']), 0)
            
            if current_location != next_meeting['location'] and current_time + travel_time <= next_meeting['start']:
                itinerary.append({
                    "action": "travel",
                    "location": next_meeting['location'],
                    "person": "",
                    "start_time": minutes_to_time(current_time),
                    "end_time": minutes_to_time(current_time + travel_time)
                })
                current_time += travel_time
                current_location = next_meeting['location']
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

def minutes_to_time(minutes):
    """Convert minutes since midnight to time string"""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

if __name__ == "__main__":
    main()