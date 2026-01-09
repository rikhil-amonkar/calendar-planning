import constraint
from datetime import datetime, timedelta
import json

def main():
    # Travel times in minutes
    travel_times = {
        ('Bayview', 'Embarcadero'): 19,
        ('Bayview', 'Richmond District'): 25,
        ('Bayview', 'Fisherman\'s Wharf'): 25,
        ('Embarcadero', 'Bayview'): 21,
        ('Embarcadero', 'Richmond District'): 21,
        ('Embarcadero', 'Fisherman\'s Wharf'): 6,
        ('Richmond District', 'Bayview'): 26,
        ('Richmond District', 'Embarcadero'): 19,
        ('Richmond District', 'Fisherman\'s Wharf'): 18,
        ('Fisherman\'s Wharf', 'Bayview'): 26,
        ('Fisherman\'s Wharf', 'Embarcadero'): 8,
        ('Fisherman\'s Wharf', 'Richmond District'): 18
    }
    
    # Convert times to minutes since 9:00 AM
    def time_to_minutes(time_str):
        if ':' in time_str:
            hours, minutes = time_str.split(':')
            am_pm = minutes[-2:]
            minutes = minutes[:-2] if am_pm in ['AM', 'PM'] else minutes
            hours = int(hours)
            minutes = int(minutes)
            
            if am_pm == 'PM' and hours != 12:
                hours += 12
            elif am_pm == 'AM' and hours == 12:
                hours = 0
                
            return hours * 60 + minutes
        return int(time_str)
    
    # Convert minutes to time string
    def minutes_to_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours}:{mins:02d}"
    
    # Friend constraints
    friends = {
        'Jessica': {
            'location': 'Embarcadero',
            'available_start': time_to_minutes('16:45'),  # 4:45 PM
            'available_end': time_to_minutes('19:00'),    # 7:00 PM
            'min_duration': 30
        },
        'Sandra': {
            'location': 'Richmond District',
            'available_start': time_to_minutes('18:30'),  # 6:30 PM
            'available_end': time_to_minutes('21:45'),    # 9:45 PM
            'min_duration': 120
        },
        'Jason': {
            'location': 'Fisherman\'s Wharf',
            'available_start': time_to_minutes('16:00'),  # 4:00 PM
            'available_end': time_to_minutes('16:45'),    # 4:45 PM
            'min_duration': 30
        }
    }
    
    start_time = time_to_minutes('9:00')  # Start at Bayview at 9:00 AM
    current_location = 'Bayview'
    
    problem = constraint.Problem()
    
    # Variables for each meeting: start time and duration
    for friend in friends:
        friend_info = friends[friend]
        problem.addVariable(f"{friend}_start", range(friend_info['available_start'], friend_info['available_end'] + 1))
        problem.addVariable(f"{friend}_duration", range(friend_info['min_duration'], friend_info['available_end'] - friend_info['available_start'] + 1))
    
    # Constraint: meeting must end within available time
    for friend in friends:
        friend_info = friends[friend]
        problem.addConstraint(
            lambda start, duration, end=friend_info['available_end']: start + duration <= end,
            [f"{friend}_start", f"{friend}_duration"]
        )
    
    # Constraint: meetings cannot overlap and must account for travel
    friend_list = list(friends.keys())
    
    def no_overlap_constraint(*args):
        # Extract start times and durations for all friends
        values = {}
        for i, friend in enumerate(friend_list):
            values[friend] = {
                'start': args[i * 2],
                'duration': args[i * 2 + 1],
                'location': friends[friend]['location']
            }
        
        # Generate all possible orders
        from itertools import permutations
        
        best_score = -1
        best_schedule = None
        
        for order in permutations(friend_list):
            current_time = start_time
            current_loc = current_location
            valid = True
            total_meeting_time = 0
            schedule = []
            
            for friend in order:
                friend_data = values[friend]
                meeting_start = friend_data['start']
                meeting_duration = friend_data['duration']
                meeting_location = friend_data['location']
                
                # Check if we can travel to this meeting
                travel_time = travel_times.get((current_loc, meeting_location), float('inf'))
                
                # Earliest we can arrive at meeting location
                earliest_arrival = current_time + travel_time
                
                # Check if we can make it to the meeting on time
                if earliest_arrival > meeting_start:
                    valid = False
                    break
                
                # Update current time and location
                current_time = meeting_start + meeting_duration
                current_loc = meeting_location
                total_meeting_time += meeting_duration
                
                schedule.append({
                    'friend': friend,
                    'start': meeting_start,
                    'duration': meeting_duration,
                    'location': meeting_location
                })
            
            if valid and total_meeting_time > best_score:
                best_score = total_meeting_time
                best_schedule = schedule
        
        return best_schedule is not None
    
    # Add all variables to the constraint
    all_vars = []
    for friend in friend_list:
        all_vars.extend([f"{friend}_start", f"{friend}_duration"])
    
    problem.addConstraint(no_overlap_constraint, all_vars)
    
    # Find solution
    solutions = problem.getSolutions()
    
    if not solutions:
        # Fallback: try to meet as many friends as possible with minimum duration
        best_solution = None
        best_meeting_time = -1
        
        for friend in friend_list:
            # Try meeting just this one friend
            meeting_time = friends[friend]['min_duration']
            if meeting_time > best_meeting_time:
                best_meeting_time = meeting_time
                best_solution = {
                    f"{friend}_start": friends[friend]['available_start'],
                    f"{friend}_duration": friends[friend]['min_duration']
                }
                for other in friend_list:
                    if other != friend:
                        best_solution[f"{other}_start"] = friends[other]['available_start']
                        best_solution[f"{other}_duration"] = 0
        
        if best_solution:
            solutions = [best_solution]
    
    if solutions:
        # Find the solution with maximum total meeting time
        best_solution = None
        max_total_time = -1
        
        for sol in solutions:
            total_time = 0
            for friend in friend_list:
                total_time += sol.get(f"{friend}_duration", 0)
            
            if total_time > max_total_time:
                max_total_time = total_time
                best_solution = sol
        
        # Build itinerary
        itinerary = []
        current_time = start_time
        current_loc = current_location
        
        # Sort meetings by start time
        meetings = []
        for friend in friend_list:
            start = best_solution.get(f"{friend}_start")
            duration = best_solution.get(f"{friend}_duration", 0)
            if duration > 0:
                meetings.append({
                    'friend': friend,
                    'start': start,
                    'duration': duration,
                    'location': friends[friend]['location']
                })
        
        meetings.sort(key=lambda x: x['start'])
        
        for meeting in meetings:
            friend = meeting['friend']
            start_time_meeting = meeting['start']
            duration = meeting['duration']
            location = meeting['location']
            
            # Add travel if needed
            if current_loc != location:
                travel_time = travel_times.get((current_loc, location), 0)
                travel_start = minutes_to_time(current_time)
                travel_end = minutes_to_time(current_time + travel_time)
                itinerary.append({
                    "action": "travel",
                    "location": location,
                    "start_time": travel_start,
                    "end_time": travel_end
                })
                current_time += travel_time
            
            # Add meeting
            meeting_start = minutes_to_time(start_time_meeting)
            meeting_end = minutes_to_time(start_time_meeting + duration)
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": friend,
                "start_time": meeting_start,
                "end_time": meeting_end
            })
            
            current_time = start_time_meeting + duration
            current_loc = location
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"itinerary": []}, indent=2))

if __name__ == "__main__":
    main()