import constraint
from datetime import datetime, timedelta
import json

def main():
    # Travel times in minutes between locations
    travel_times = {
        ('Nob Hill', 'Presidio'): 17,
        ('Nob Hill', 'North Beach'): 8,
        ('Nob Hill', 'Fisherman\'s Wharf'): 11,
        ('Nob Hill', 'Pacific Heights'): 8,
        ('Presidio', 'Nob Hill'): 18,
        ('Presidio', 'North Beach'): 18,
        ('Presidio', 'Fisherman\'s Wharf'): 19,
        ('Presidio', 'Pacific Heights'): 11,
        ('North Beach', 'Nob Hill'): 7,
        ('North Beach', 'Presidio'): 17,
        ('North Beach', 'Fisherman\'s Wharf'): 5,
        ('North Beach', 'Pacific Heights'): 8,
        ('Fisherman\'s Wharf', 'Nob Hill'): 11,
        ('Fisherman\'s Wharf', 'Presidio'): 17,
        ('Fisherman\'s Wharf', 'North Beach'): 6,
        ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
        ('Pacific Heights', 'Nob Hill'): 8,
        ('Pacific Heights', 'Presidio'): 11,
        ('Pacific Heights', 'North Beach'): 9,
        ('Pacific Heights', 'Fisherman\'s Wharf'): 13
    }
    
    # Convert all times to minutes since 9:00 AM (540 minutes)
    start_time_base = 540  # 9:00 AM in minutes
    
    # Friend constraints: (location, start_min, end_min, duration_min)
    friends = {
        'Jeffrey': ('Presidio', 480, 600, 105),    # 8:00-10:00 AM, 105 min
        'Steven': ('North Beach', 810, 1320, 45),  # 1:30-10:00 PM, 45 min
        'Barbara': ('Fisherman\'s Wharf', 1080, 1290, 30),  # 6:00-9:30 PM, 30 min
        'John': ('Pacific Heights', 540, 810, 15)  # 9:00 AM-1:30 PM, 15 min
    }
    
    # Create problem
    problem = constraint.Problem()
    
    # Variables: start time for each meeting (in minutes since 9:00 AM)
    for friend in friends:
        location, friend_start, friend_end, duration = friends[friend]
        # Meeting must start within friend's availability window minus duration
        problem.addVariable(f"{friend}_start", range(friend_start, friend_end - duration + 1))
        problem.addVariable(f"{friend}_duration", [duration])
    
    # Helper function to check if two meetings can be scheduled consecutively
    def can_schedule_consecutive(friend1, friend2):
        loc1 = friends[friend1][0]
        loc2 = friends[friend2][0]
        travel_time = travel_times.get((loc1, loc2), 0)
        
        def constraint_func(f1_start, f1_dur, f2_start, f2_dur):
            f1_end = f1_start + f1_dur
            f2_end = f2_start + f2_dur  # Fixed: Added this line
            # Either friend2 starts after friend1 ends plus travel time
            # Or friend1 starts after friend2 ends plus travel time
            return (f2_start >= f1_end + travel_time) or (f1_start >= f2_end + travel_time)
        
        return constraint_func
    
    # Add constraints for all pairs of friends
    friend_names = list(friends.keys())
    for i in range(len(friend_names)):
        for j in range(i + 1, len(friend_names)):
            friend1 = friend_names[i]
            friend2 = friend_names[j]
            problem.addConstraint(
                can_schedule_consecutive(friend1, friend2),
                [f"{friend1}_start", f"{friend1}_duration", f"{friend2}_start", f"{friend2}_duration"]
            )
    
    # Additional constraint: you start at Nob Hill at 9:00 AM
    def first_meeting_constraint(*starts_and_durations):
        # Find the earliest meeting start time
        earliest_start = min(starts_and_durations[::2])
        first_meeting_friend = None
        for i, friend in enumerate(friend_names):
            if starts_and_durations[i * 2] == earliest_start:
                first_meeting_friend = friend
                break
        
        if first_meeting_friend:
            first_location = friends[first_meeting_friend][0]
            travel_from_nob_hill = travel_times.get(('Nob Hill', first_location), 0)
            return earliest_start >= start_time_base + travel_from_nob_hill
        return False
    
    # Prepare variable list for constraint
    var_list = []
    for friend in friend_names:
        var_list.append(f"{friend}_start")
        var_list.append(f"{friend}_duration")
    
    problem.addConstraint(first_meeting_constraint, var_list)
    
    # Find solutions
    solutions = problem.getSolutions()
    
    if not solutions:
        # Fallback: try to schedule meetings one by one in a greedy approach
        itinerary = greedy_schedule(friends, travel_times, start_time_base)
    else:
        # Find the solution with the most meetings scheduled
        best_solution = None
        max_meetings = 0
        
        for solution in solutions:
            scheduled_meetings = 0
            for friend in friend_names:
                if solution.get(f"{friend}_start") is not None:
                    scheduled_meetings += 1
            
            if scheduled_meetings > max_meetings:
                max_meetings = scheduled_meetings
                best_solution = solution
        
        # Convert best solution to itinerary
        itinerary = []
        for friend in friend_names:
            if f"{friend}_start" in best_solution:
                start_min = best_solution[f"{friend}_start"]
                duration = best_solution[f"{friend}_duration"]
                location = friends[friend][0]
                
                start_time = minutes_to_time(start_min)
                end_time = minutes_to_time(start_min + duration)
                
                itinerary.append({
                    "action": "meet",
                    "location": location,
                    "person": friend,
                    "start_time": start_time,
                    "end_time": end_time
                })
        
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: time_to_minutes(x["start_time"]))
    
    # Output as JSON
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))

def greedy_schedule(friends, travel_times, start_time_base):
    """Fallback greedy scheduling algorithm"""
    current_time = start_time_base
    current_location = 'Nob Hill'
    scheduled = set()
    itinerary = []
    
    # Try to schedule meetings in order of availability
    friend_order = ['John', 'Jeffrey', 'Steven', 'Barbara']  # Based on time windows
    
    for friend in friend_order:
        if friend in scheduled:
            continue
            
        location, friend_start, friend_end, duration = friends[friend]
        
        # Calculate travel time to this location
        travel_time = travel_times.get((current_location, location), 0)
        
        # Earliest we can start this meeting
        earliest_start = max(current_time + travel_time, friend_start)
        
        # Check if we can fit this meeting
        if earliest_start + duration <= friend_end:
            start_time_str = minutes_to_time(earliest_start)
            end_time_str = minutes_to_time(earliest_start + duration)
            
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": friend,
                "start_time": start_time_str,
                "end_time": end_time_str
            })
            
            scheduled.add(friend)
            current_time = earliest_start + duration
            current_location = location
    
    return itinerary

def time_to_minutes(time_str):
    """Convert time string (H:MM) to minutes since midnight"""
    if isinstance(time_str, int):
        return time_str
    
    time_obj = datetime.strptime(time_str, '%H:%M')
    return time_obj.hour * 60 + time_obj.minute

def minutes_to_time(minutes):
    """Convert minutes since midnight to time string (H:MM)"""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

if __name__ == "__main__":
    main()