import constraint
from datetime import datetime, timedelta
import json

def time_to_minutes(time_str):
    """Convert time string (H:MM) to minutes since midnight"""
    dt = datetime.strptime(time_str, '%H:%M')
    return dt.hour * 60 + dt.minute

def minutes_to_time(minutes):
    """Convert minutes since midnight to time string (H:MM)"""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    # Travel times in minutes (from row to column)
    travel_times = {
        'Financial District': {
            'Financial District': 0,
            'Russian Hill': 10,
            'Sunset District': 31,
            'North Beach': 7,
            'The Castro': 23,
            'Golden Gate Park': 23
        },
        'Russian Hill': {
            'Financial District': 11,
            'Russian Hill': 0,
            'Sunset District': 23,
            'North Beach': 5,
            'The Castro': 21,
            'Golden Gate Park': 21
        },
        'Sunset District': {
            'Financial District': 30,
            'Russian Hill': 24,
            'Sunset District': 0,
            'North Beach': 29,
            'The Castro': 17,
            'Golden Gate Park': 11
        },
        'North Beach': {
            'Financial District': 8,
            'Russian Hill': 4,
            'Sunset District': 27,
            'North Beach': 0,
            'The Castro': 22,
            'Golden Gate Park': 22
        },
        'The Castro': {
            'Financial District': 20,
            'Russian Hill': 18,
            'Sunset District': 17,
            'North Beach': 20,
            'The Castro': 0,
            'Golden Gate Park': 11
        },
        'Golden Gate Park': {
            'Financial District': 26,
            'Russian Hill': 19,
            'Sunset District': 10,
            'North Beach': 24,
            'The Castro': 13,
            'Golden Gate Park': 0
        }
    }

    # Friend constraints
    friends = {
        'Ronald': {
            'location': 'Russian Hill',
            'available_start': time_to_minutes('13:45'),  # 1:45 PM
            'available_end': time_to_minutes('17:15'),    # 5:15 PM
            'min_duration': 105
        },
        'Patricia': {
            'location': 'Sunset District',
            'available_start': time_to_minutes('9:15'),   # 9:15 AM
            'available_end': time_to_minutes('22:00'),    # 10:00 PM
            'min_duration': 60
        },
        'Laura': {
            'location': 'North Beach',
            'available_start': time_to_minutes('12:30'),  # 12:30 PM
            'available_end': time_to_minutes('12:45'),    # 12:45 PM
            'min_duration': 15
        },
        'Emily': {
            'location': 'The Castro',
            'available_start': time_to_minutes('16:15'),  # 4:15 PM
            'available_end': time_to_minutes('18:30'),    # 6:30 PM
            'min_duration': 60
        },
        'Mary': {
            'location': 'Golden Gate Park',
            'available_start': time_to_minutes('15:00'),  # 3:00 PM
            'available_end': time_to_minutes('16:30'),    # 4:30 PM
            'min_duration': 60
        }
    }

    # Start at Financial District at 9:00 AM
    start_time = time_to_minutes('9:00')
    current_location = 'Financial District'
    max_end_time = time_to_minutes('22:00')  # End of day constraint

    problem = constraint.Problem()

    # Define variables for each friend: start time and duration
    friend_vars = {}
    for friend in friends:
        friend_vars[friend] = {
            'start': f"{friend}_start",
            'duration': f"{friend}_duration"
        }
        available_start = friends[friend]['available_start']
        available_end = friends[friend]['available_end']
        min_duration = friends[friend]['min_duration']
        
        # Start time must be within available window
        problem.addVariable(f"{friend}_start", range(available_start, available_end + 1))
        # Duration must be at least minimum required
        problem.addVariable(f"{friend}_duration", range(min_duration, (available_end - available_start) + 1))

    # Add constraints for time ordering and travel
    friend_names = list(friends.keys())
    
    def time_constraints(*args):
        # Create a list of (friend, start_time, duration) tuples
        schedule = []
        for i, friend in enumerate(friend_names):
            start_idx = i * 2
            duration_idx = i * 2 + 1
            schedule.append((friend, args[start_idx], args[duration_idx]))
        
        # Sort by start time
        schedule.sort(key=lambda x: x[1])
        
        current_time = start_time
        current_loc = current_location
        
        for i, (friend, start, duration) in enumerate(schedule):
            # Check if meeting fits within friend's availability
            friend_info = friends[friend]
            if start < friend_info['available_start'] or start + duration > friend_info['available_end']:
                return False
            
            # Check travel time from previous location
            if i == 0:
                # First meeting - travel from start location
                travel_time = travel_times[current_loc][friend_info['location']]
                if start < current_time + travel_time:
                    return False
            else:
                # Subsequent meetings - travel from previous meeting location
                prev_friend = schedule[i-1][0]
                prev_location = friends[prev_friend]['location']
                travel_time = travel_times[prev_location][friend_info['location']]
                prev_end = schedule[i-1][1] + schedule[i-1][2]
                if start < prev_end + travel_time:
                    return False
            
            # Update current location and time
            current_loc = friend_info['location']
            current_time = start + duration
            
            # Check if we exceed end of day
            if current_time > max_end_time:
                return False
        
        return True

    # Get all variable names for the constraint function
    all_vars = []
    for friend in friend_names:
        all_vars.append(friend_vars[friend]['start'])
        all_vars.append(friend_vars[friend]['duration'])
    
    problem.addConstraint(time_constraints, all_vars)

    # Find solutions - we want to maximize number of friends met
    solutions = problem.getSolutions()
    
    if not solutions:
        # If no solution meeting all friends, try subsets
        best_solution = None
        best_count = 0
        
        # Try all subsets of friends
        from itertools import combinations
        for r in range(len(friend_names), 0, -1):
            for subset in combinations(friend_names, r):
                sub_problem = constraint.Problem()
                sub_vars = []
                
                for friend in subset:
                    available_start = friends[friend]['available_start']
                    available_end = friends[friend]['available_end']
                    min_duration = friends[friend]['min_duration']
                    
                    sub_problem.addVariable(f"{friend}_start", range(available_start, available_end + 1))
                    sub_problem.addVariable(f"{friend}_duration", range(min_duration, (available_end - available_start) + 1))
                    sub_vars.append(f"{friend}_start")
                    sub_vars.append(f"{friend}_duration")
                
                def sub_time_constraints(*args):
                    schedule = []
                    for i, friend in enumerate(subset):
                        start_idx = i * 2
                        duration_idx = i * 2 + 1
                        schedule.append((friend, args[start_idx], args[duration_idx]))
                    
                    schedule.sort(key=lambda x: x[1])
                    
                    current_time = start_time
                    current_loc = current_location
                    
                    for i, (friend, start, duration) in enumerate(schedule):
                        friend_info = friends[friend]
                        if start < friend_info['available_start'] or start + duration > friend_info['available_end']:
                            return False
                        
                        if i == 0:
                            travel_time = travel_times[current_loc][friend_info['location']]
                            if start < current_time + travel_time:
                                return False
                        else:
                            prev_friend = schedule[i-1][0]
                            prev_location = friends[prev_friend]['location']
                            travel_time = travel_times[prev_location][friend_info['location']]
                            prev_end = schedule[i-1][1] + schedule[i-1][2]
                            if start < prev_end + travel_time:
                                return False
                        
                        current_loc = friend_info['location']
                        current_time = start + duration
                        
                        if current_time > max_end_time:
                            return False
                    
                    return True
                
                sub_problem.addConstraint(sub_time_constraints, sub_vars)
                sub_solutions = sub_problem.getSolutions()
                
                if sub_solutions:
                    # Use the first valid solution for this subset
                    best_solution = sub_solutions[0]
                    best_count = len(subset)
                    break
            
            if best_solution:
                break
        
        if not best_solution:
            # Fallback: empty itinerary
            result = {"itinerary": []}
            print(json.dumps(result, indent=2))
            return
        
        solution = best_solution
        used_friends = subset
    else:
        solution = solutions[0]
        used_friends = friend_names

    # Build itinerary from solution
    itinerary = []
    
    # Create list of meetings with their times
    meetings = []
    for friend in used_friends:
        start_time_val = solution[f"{friend}_start"]
        duration_val = solution[f"{friend}_duration"]
        meetings.append({
            'friend': friend,
            'location': friends[friend]['location'],
            'start': start_time_val,
            'end': start_time_val + duration_val,
            'duration': duration_val
        })
    
    # Sort meetings by start time
    meetings.sort(key=lambda x: x['start'])
    
    # Add travel from start location to first meeting
    if meetings:
        first_meeting = meetings[0]
        travel_start = start_time
        travel_end = first_meeting['start']
        if travel_end > travel_start:
            itinerary.append({
                "action": "travel",
                "location": first_meeting['location'],
                "person": "",
                "start_time": minutes_to_time(travel_start),
                "end_time": minutes_to_time(travel_end)
            })
    
    # Add meetings
    for i, meeting in enumerate(meetings):
        itinerary.append({
            "action": "meet",
            "location": meeting['location'],
            "person": meeting['friend'],
            "start_time": minutes_to_time(meeting['start']),
            "end_time": minutes_to_time(meeting['end'])
        })
        
        # Add travel to next meeting if there is one
        if i < len(meetings) - 1:
            next_meeting = meetings[i + 1]
            travel_time_needed = travel_times[meeting['location']][next_meeting['location']]
            travel_start = meeting['end']
            travel_end = next_meeting['start']
            
            if travel_end > travel_start:
                itinerary.append({
                    "action": "travel",
                    "location": next_meeting['location'],
                    "person": "",
                    "start_time": minutes_to_time(travel_start),
                    "end_time": minutes_to_time(travel_end)
                })

    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()