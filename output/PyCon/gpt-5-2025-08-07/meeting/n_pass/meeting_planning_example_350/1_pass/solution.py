import constraint
from datetime import datetime, timedelta
import json

def main():
    # Travel times in minutes between locations
    travel_times = {
        ('Bayview', 'Pacific Heights'): 23,
        ('Bayview', 'Mission District'): 13,
        ('Bayview', 'Haight-Ashbury'): 19,
        ('Bayview', 'Financial District'): 19,
        ('Pacific Heights', 'Bayview'): 22,
        ('Pacific Heights', 'Mission District'): 15,
        ('Pacific Heights', 'Haight-Ashbury'): 11,
        ('Pacific Heights', 'Financial District'): 13,
        ('Mission District', 'Bayview'): 15,
        ('Mission District', 'Pacific Heights'): 16,
        ('Mission District', 'Haight-Ashbury'): 12,
        ('Mission District', 'Financial District'): 17,
        ('Haight-Ashbury', 'Bayview'): 18,
        ('Haight-Ashbury', 'Pacific Heights'): 12,
        ('Haight-Ashbury', 'Mission District'): 11,
        ('Haight-Ashbury', 'Financial District'): 21,
        ('Financial District', 'Bayview'): 19,
        ('Financial District', 'Pacific Heights'): 13,
        ('Financial District', 'Mission District'): 17,
        ('Financial District', 'Haight-Ashbury'): 19
    }
    
    # Convert times to minutes since midnight for easier computation
    def time_to_minutes(time_str):
        if 'AM' in time_str or 'PM' in time_str:
            time_obj = datetime.strptime(time_str, '%I:%M%p')
        else:
            time_obj = datetime.strptime(time_str, '%H:%M')
        return time_obj.hour * 60 + time_obj.minute
    
    # Convert minutes back to time string
    def minutes_to_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours}:{mins:02d}"
    
    # Friend constraints
    friends = {
        'Mary': {
            'location': 'Pacific Heights',
            'available_start': time_to_minutes('10:00AM'),
            'available_end': time_to_minutes('7:00PM'),
            'duration': 45
        },
        'Lisa': {
            'location': 'Mission District',
            'available_start': time_to_minutes('8:30PM'),
            'available_end': time_to_minutes('10:00PM'),
            'duration': 75
        },
        'Betty': {
            'location': 'Haight-Ashbury',
            'available_start': time_to_minutes('7:15AM'),
            'available_end': time_to_minutes('5:15PM'),
            'duration': 90
        },
        'Charles': {
            'location': 'Financial District',
            'available_start': time_to_minutes('11:15AM'),
            'available_end': time_to_minutes('3:00PM'),
            'duration': 120
        }
    }
    
    start_location = 'Bayview'
    start_time = time_to_minutes('9:00AM')
    
    # Create problem
    problem = constraint.Problem()
    
    # Variables: start time for each meeting
    friend_names = list(friends.keys())
    for friend in friend_names:
        friend_info = friends[friend]
        problem.addVariable(f'{friend}_start', 
                           range(friend_info['available_start'], 
                                 friend_info['available_end'] - friend_info['duration'] + 1))
    
    # Generate all permutations of meeting order
    from itertools import permutations
    
    best_schedule = None
    max_meetings = 0
    
    # Try all possible orders of meetings
    for order in permutations(friend_names):
        temp_problem = constraint.Problem()
        
        # Add variables
        for friend in friend_names:
            friend_info = friends[friend]
            temp_problem.addVariable(f'{friend}_start', 
                                   range(friend_info['available_start'], 
                                         friend_info['available_end'] - friend_info['duration'] + 1))
        
        # Add constraints for travel time between consecutive meetings
        current_location = start_location
        current_time = start_time
        
        for i, friend in enumerate(order):
            friend_info = friends[friend]
            location = friend_info['location']
            
            # Travel time constraint
            travel_time = travel_times.get((current_location, location), 0)
            
            # The meeting must start after travel time from previous location
            if i == 0:
                # First meeting constraint
                temp_problem.addConstraint(
                    lambda start, travel=travel_time, curr=current_time: start >= curr + travel,
                    [f'{friend}_start']
                )
            else:
                prev_friend = order[i-1]
                prev_friend_info = friends[prev_friend]
                
                def constraint_fn(prev_start, curr_start, prev_dur=prev_friend_info['duration'], trav=travel_time):
                    return curr_start >= prev_start + prev_dur + trav
                
                temp_problem.addConstraint(
                    constraint_fn,
                    [f'{prev_friend}_start', f'{friend}_start']
                )
            
            current_location = location
        
        # Try to find a solution
        solutions = temp_problem.getSolutions()
        
        if solutions:
            # Count how many meetings we can have in this order
            valid_meetings = []
            current_loc = start_location
            current_time_val = start_time
            
            for friend in order:
                friend_info = friends[friend]
                start_time_val = solutions[0][f'{friend}_start']
                end_time_val = start_time_val + friend_info['duration']
                
                # Check if meeting fits in availability
                if (start_time_val >= friend_info['available_start'] and 
                    end_time_val <= friend_info['available_end']):
                    
                    # Check travel time
                    travel_time_val = travel_times.get((current_loc, friend_info['location']), 0)
                    if start_time_val >= current_time_val + travel_time_val:
                        valid_meetings.append(friend)
                        current_loc = friend_info['location']
                        current_time_val = end_time_val
                    else:
                        break
                else:
                    break
            
            if len(valid_meetings) > max_meetings:
                max_meetings = len(valid_meetings)
                best_schedule = (order[:len(valid_meetings)], solutions[0])
    
    # Build the itinerary
    itinerary = []
    if best_schedule:
        order, solution = best_schedule
        current_location = start_location
        current_time = start_time
        
        for friend in order:
            friend_info = friends[friend]
            start_time_val = solution[f'{friend}_start']
            end_time_val = start_time_val + friend_info['duration']
            
            # Add travel if needed
            if current_location != friend_info['location']:
                travel_duration = travel_times[(current_location, friend_info['location'])]
                travel_start = current_time
                travel_end = current_time + travel_duration
                
                itinerary.append({
                    "action": "travel",
                    "location": friend_info['location'],
                    "person": None,
                    "start_time": minutes_to_time(travel_start),
                    "end_time": minutes_to_time(travel_end)
                })
            
            # Add meeting
            itinerary.append({
                "action": "meet",
                "location": friend_info['location'],
                "person": friend,
                "start_time": minutes_to_time(start_time_val),
                "end_time": minutes_to_time(end_time_val)
            })
            
            current_location = friend_info['location']
            current_time = end_time_val
    
    # Output as JSON
    result = {
        "itinerary": itinerary
    }
    
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()