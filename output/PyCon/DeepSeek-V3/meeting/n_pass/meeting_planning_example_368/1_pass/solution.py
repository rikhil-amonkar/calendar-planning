import constraint
from datetime import datetime, timedelta
import json

def main():
    # Travel times in minutes between locations
    travel_times = {
        ('Bayview', 'Russian Hill'): 23,
        ('Bayview', 'Alamo Square'): 16,
        ('Bayview', 'North Beach'): 21,
        ('Bayview', 'Financial District'): 19,
        ('Russian Hill', 'Bayview'): 23,
        ('Russian Hill', 'Alamo Square'): 15,
        ('Russian Hill', 'North Beach'): 5,
        ('Russian Hill', 'Financial District'): 11,
        ('Alamo Square', 'Bayview'): 16,
        ('Alamo Square', 'Russian Hill'): 13,
        ('Alamo Square', 'North Beach'): 15,
        ('Alamo Square', 'Financial District'): 17,
        ('North Beach', 'Bayview'): 22,
        ('North Beach', 'Russian Hill'): 4,
        ('North Beach', 'Alamo Square'): 16,
        ('North Beach', 'Financial District'): 8,
        ('Financial District', 'Bayview'): 19,
        ('Financial District', 'Russian Hill'): 10,
        ('Financial District', 'Alamo Square'): 17,
        ('Financial District', 'North Beach'): 7
    }
    
    # Convert all times to minutes since 9:00 AM
    base_time = datetime(2024, 1, 1, 9, 0)  # Starting at 9:00 AM
    
    # Friend availability windows (in minutes from 9:00 AM)
    availability = {
        'Joseph': {
            'location': 'Russian Hill',
            'start': time_to_minutes('8:30') - time_to_minutes('9:00'),  # -30 minutes
            'end': time_to_minutes('19:15') - time_to_minutes('9:00'),   # 615 minutes
            'duration': 60
        },
        'Nancy': {
            'location': 'Alamo Square', 
            'start': time_to_minutes('11:00') - time_to_minutes('9:00'),  # 120 minutes
            'end': time_to_minutes('16:00') - time_to_minutes('9:00'),    # 420 minutes
            'duration': 90
        },
        'Jason': {
            'location': 'North Beach',
            'start': time_to_minutes('16:45') - time_to_minutes('9:00'),  # 465 minutes
            'end': time_to_minutes('21:45') - time_to_minutes('9:00'),    # 765 minutes
            'duration': 15
        },
        'Jeffrey': {
            'location': 'Financial District',
            'start': time_to_minutes('10:30') - time_to_minutes('9:00'),  # 90 minutes
            'end': time_to_minutes('15:45') - time_to_minutes('9:00'),    # 405 minutes
            'duration': 45
        }
    }
    
    # Create problem
    problem = constraint.Problem()
    
    # Define variables for start times of each meeting
    friends = ['Joseph', 'Nancy', 'Jason', 'Jeffrey']
    
    # Add variables for start times (in minutes from 9:00)
    for friend in friends:
        friend_info = availability[friend]
        problem.addVariable(f'{friend}_start', 
                          range(friend_info['start'], 
                                friend_info['end'] - friend_info['duration'] + 1))
    
    # Add constraint: meetings must not overlap when considering travel
    def no_overlap_with_travel(*starts):
        starts_dict = {}
        for i, friend in enumerate(friends):
            starts_dict[friend] = starts[i]
        
        # Sort meetings by start time
        ordered_friends = sorted(friends, key=lambda f: starts_dict[f])
        
        for i in range(len(ordered_friends) - 1):
            current_friend = ordered_friends[i]
            next_friend = ordered_friends[i + 1]
            
            current_end = starts_dict[current_friend] + availability[current_friend]['duration']
            travel_time = travel_times[(availability[current_friend]['location'], 
                                      availability[next_friend]['location'])]
            
            if current_end + travel_time > starts_dict[next_friend]:
                return False
        
        return True
    
    problem.addConstraint(no_overlap_with_travel, [f'{f}_start' for f in friends])
    
    # Add constraint: all meetings must fit within their availability windows
    def within_availability(*starts):
        for i, friend in enumerate(friends):
            friend_info = availability[friend]
            if starts[i] < friend_info['start'] or starts[i] + friend_info['duration'] > friend_info['end']:
                return False
        return True
    
    problem.addConstraint(within_availability, [f'{f}_start' for f in friends])
    
    # Find solutions
    solutions = problem.getSolutions()
    
    if not solutions:
        # Fallback: try to find a solution with fewer meetings
        best_solution = None
        max_meetings = 0
        
        # Try all combinations of 3 friends
        for combo_size in range(4, 0, -1):
            from itertools import combinations
            for friend_combo in combinations(friends, combo_size):
                sub_problem = constraint.Problem()
                
                for friend in friend_combo:
                    friend_info = availability[friend]
                    sub_problem.addVariable(f'{friend}_start', 
                                          range(friend_info['start'], 
                                                friend_info['end'] - friend_info['duration'] + 1))
                
                def sub_no_overlap(*starts):
                    starts_dict = {}
                    for i, friend in enumerate(friend_combo):
                        starts_dict[friend] = starts[i]
                    
                    ordered_friends = sorted(friend_combo, key=lambda f: starts_dict[f])
                    
                    for i in range(len(ordered_friends) - 1):
                        current_friend = ordered_friends[i]
                        next_friend = ordered_friends[i + 1]
                        
                        current_end = starts_dict[current_friend] + availability[current_friend]['duration']
                        travel_time = travel_times[(availability[current_friend]['location'], 
                                                  availability[next_friend]['location'])]
                        
                        if current_end + travel_time > starts_dict[next_friend]:
                            return False
                    
                    return True
                
                sub_problem.addConstraint(sub_no_overlap, [f'{f}_start' for f in friend_combo])
                sub_solutions = sub_problem.getSolutions()
                
                if sub_solutions:
                    best_solution = sub_solutions[0]
                    max_meetings = combo_size
                    break
            
            if best_solution:
                break
        
        if not best_solution:
            # Return empty itinerary if no solution found
            print(json.dumps({"itinerary": []}))
            return
            
        solution = best_solution
        used_friends = friend_combo if 'friend_combo' in locals() else friends
    else:
        solution = solutions[0]
        used_friends = friends
    
    # Build itinerary
    itinerary = []
    
    # Sort meetings by start time
    ordered_meetings = sorted(used_friends, key=lambda f: solution[f'{f}_start'])
    
    # Add travel from starting location (Bayview) to first meeting
    first_friend = ordered_meetings[0]
    first_location = availability[first_friend]['location']
    travel_from_start = travel_times[('Bayview', first_location)]
    
    # Create itinerary items
    for i, friend in enumerate(ordered_meetings):
        friend_info = availability[friend]
        start_minutes = solution[f'{friend}_start']
        end_minutes = start_minutes + friend_info['duration']
        
        # Convert minutes to time strings
        start_time = minutes_to_time(start_minutes + time_to_minutes('9:00'))
        end_time = minutes_to_time(end_minutes + time_to_minutes('9:00'))
        
        itinerary.append({
            "action": "meet",
            "location": friend_info['location'],
            "person": friend,
            "start_time": start_time,
            "end_time": end_time
        })
    
    # Output result
    result = {
        "itinerary": itinerary
    }
    
    print(json.dumps(result, indent=2))

def time_to_minutes(time_str):
    """Convert time string (H:MM) to minutes since midnight"""
    time_obj = datetime.strptime(time_str, '%H:%M')
    return time_obj.hour * 60 + time_obj.minute

def minutes_to_time(minutes):
    """Convert minutes since midnight to time string (H:MM)"""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

if __name__ == "__main__":
    main()