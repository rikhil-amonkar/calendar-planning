import constraint
from datetime import datetime, timedelta
import json

def time_to_minutes(time_str):
    """Convert time string (H:MM) to minutes since midnight"""
    time_obj = datetime.strptime(time_str, '%H:%M')
    return time_obj.hour * 60 + time_obj.minute

def minutes_to_time(minutes):
    """Convert minutes since midnight to time string (H:MM)"""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    # Travel times dictionary (in minutes)
    travel_times = {
        ('Golden Gate Park', 'Haight-Ashbury'): 7,
        ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
        ('Golden Gate Park', 'The Castro'): 13,
        ('Golden Gate Park', 'Chinatown'): 23,
        ('Golden Gate Park', 'Alamo Square'): 10,
        ('Golden Gate Park', 'North Beach'): 24,
        ('Golden Gate Park', 'Russian Hill'): 19,
        ('Haight-Ashbury', 'Golden Gate Park'): 7,
        ('Haight-Ashbury', 'Fisherman\'s Wharf'): 23,
        ('Haight-Ashbury', 'The Castro'): 6,
        ('Haight-Ashbury', 'Chinatown'): 19,
        ('Haight-Ashbury', 'Alamo Square'): 5,
        ('Haight-Ashbury', 'North Beach'): 19,
        ('Haight-Ashbury', 'Russian Hill'): 17,
        ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
        ('Fisherman\'s Wharf', 'Haight-Ashbury'): 22,
        ('Fisherman\'s Wharf', 'The Castro'): 26,
        ('Fisherman\'s Wharf', 'Chinatown'): 12,
        ('Fisherman\'s Wharf', 'Alamo Square'): 20,
        ('Fisherman\'s Wharf', 'North Beach'): 6,
        ('Fisherman\'s Wharf', 'Russian Hill'): 7,
        ('The Castro', 'Golden Gate Park'): 11,
        ('The Castro', 'Haight-Ashbury'): 6,
        ('The Castro', 'Fisherman\'s Wharf'): 24,
        ('The Castro', 'Chinatown'): 20,
        ('The Castro', 'Alamo Square'): 8,
        ('The Castro', 'North Beach'): 20,
        ('The Castro', 'Russian Hill'): 18,
        ('Chinatown', 'Golden Gate Park'): 23,
        ('Chinatown', 'Haight-Ashbury'): 19,
        ('Chinatown', 'Fisherman\'s Wharf'): 8,
        ('Chinatown', 'The Castro'): 22,
        ('Chinatown', 'Alamo Square'): 17,
        ('Chinatown', 'North Beach'): 3,
        ('Chinatown', 'Russian Hill'): 7,
        ('Alamo Square', 'Golden Gate Park'): 9,
        ('Alamo Square', 'Haight-Ashbury'): 5,
        ('Alamo Square', 'Fisherman\'s Wharf'): 19,
        ('Alamo Square', 'The Castro'): 8,
        ('Alamo Square', 'Chinatown'): 16,
        ('Alamo Square', 'North Beach'): 15,
        ('Alamo Square', 'Russian Hill'): 13,
        ('North Beach', 'Golden Gate Park'): 22,
        ('North Beach', 'Haight-Ashbury'): 18,
        ('North Beach', 'Fisherman\'s Wharf'): 5,
        ('North Beach', 'The Castro'): 22,
        ('North Beach', 'Chinatown'): 6,
        ('North Beach', 'Alamo Square'): 16,
        ('North Beach', 'Russian Hill'): 4,
        ('Russian Hill', 'Golden Gate Park'): 21,
        ('Russian Hill', 'Haight-Ashbury'): 17,
        ('Russian Hill', 'Fisherman\'s Wharf'): 7,
        ('Russian Hill', 'The Castro'): 21,
        ('Russian Hill', 'Chinatown'): 9,
        ('Russian Hill', 'Alamo Square'): 15,
        ('Russian Hill', 'North Beach'): 5
    }

    # Friend constraints
    friends = [
        {'name': 'Carol', 'location': 'Haight-Ashbury', 'available_start': '21:30', 'available_end': '22:30', 'min_duration': 60},
        {'name': 'Laura', 'location': 'Fisherman\'s Wharf', 'available_start': '11:45', 'available_end': '21:30', 'min_duration': 60},
        {'name': 'Karen', 'location': 'The Castro', 'available_start': '7:15', 'available_end': '14:00', 'min_duration': 75},
        {'name': 'Elizabeth', 'location': 'Chinatown', 'available_start': '12:15', 'available_end': '21:30', 'min_duration': 75},
        {'name': 'Deborah', 'location': 'Alamo Square', 'available_start': '12:00', 'available_end': '15:00', 'min_duration': 105},
        {'name': 'Jason', 'location': 'North Beach', 'available_start': '14:45', 'available_end': '19:00', 'min_duration': 90},
        {'name': 'Steven', 'location': 'Russian Hill', 'available_start': '14:45', 'available_end': '18:30', 'min_duration': 120}
    ]

    # Convert all times to minutes
    start_time_minutes = time_to_minutes('9:00')
    
    for friend in friends:
        friend['available_start_min'] = time_to_minutes(friend['available_start'])
        friend['available_end_min'] = time_to_minutes(friend['available_end'])

    # Create problem
    problem = constraint.Problem()

    # Variables: start time for each meeting (in minutes from midnight)
    for friend in friends:
        problem.addVariable(f"{friend['name']}_start", range(0, 24*60))

    # Constraints
    for i, friend in enumerate(friends):
        # Meeting must be within friend's availability
        problem.addConstraint(
            lambda start, f=friend: start >= f['available_start_min'] and start + f['min_duration'] <= f['available_end_min'],
            [f"{friend['name']}_start"]
        )

    # Order constraints based on logical sequence
    # Start at Golden Gate Park
    current_location = 'Golden Gate Park'
    current_time = start_time_minutes
    
    # Try to meet friends in a logical order based on time constraints
    # Karen (The Castro) is only available until 2:00 PM, so meet her early
    # Deborah (Alamo Square) is only available until 3:00 PM
    # Jason and Steven are available from 2:45 PM
    # Laura and Elizabeth are available all afternoon/evening
    # Carol is only available late evening
    
    # Define a preferred order based on time constraints
    preferred_order = ['Karen', 'Deborah', 'Jason', 'Steven', 'Laura', 'Elizabeth', 'Carol']
    
    for i in range(len(preferred_order) - 1):
        friend1 = next(f for f in friends if f['name'] == preferred_order[i])
        friend2 = next(f for f in friends if f['name'] == preferred_order[i + 1])
        
        travel_time = travel_times.get((friend1['location'], friend2['location']), 30)
        
        problem.addConstraint(
            lambda start1, start2, f1=friend1, f2=friend2, tt=travel_time: 
                start1 + f1['min_duration'] + tt <= start2,
            [f"{friend1['name']}_start", f"{friend2['name']}_start"]
        )

    # Add constraint that we start after arriving at Golden Gate Park
    first_friend = next(f for f in friends if f['name'] == preferred_order[0])
    travel_to_first = travel_times.get(('Golden Gate Park', first_friend['location']), 30)
    problem.addConstraint(
        lambda start: start >= current_time + travel_to_first,
        [f"{first_friend['name']}_start"]
    )

    # Objective: maximize number of meetings (all meetings should be scheduled)
    solutions = problem.getSolutions()
    
    if not solutions:
        # If no solution found with all meetings, try to find one with maximum meetings
        # This is a simplified approach - in a real scenario, we'd use optimization
        best_solution = None
        max_meetings = 0
        
        # Try different combinations
        for num_meetings in range(len(friends), 0, -1):
            # This is a simplified approach - a real implementation would be more sophisticated
            temp_problem = constraint.Problem()
            
            # Add subset of friends
            for i in range(num_meetings):
                friend = friends[i]
                temp_problem.addVariable(f"{friend['name']}_start", range(0, 24*60))
                
                # Meeting must be within friend's availability
                temp_problem.addConstraint(
                    lambda start, f=friend: start >= f['available_start_min'] and start + f['min_duration'] <= f['available_end_min'],
                    [f"{friend['name']}_start"]
                )
            
            # Add travel constraints for the subset
            for i in range(num_meetings - 1):
                friend1 = friends[i]
                friend2 = friends[i + 1]
                
                travel_time = travel_times.get((friend1['location'], friend2['location']), 30)
                
                temp_problem.addConstraint(
                    lambda start1, start2, f1=friend1, f2=friend2, tt=travel_time: 
                        start1 + f1['min_duration'] + tt <= start2,
                    [f"{friend1['name']}_start", f"{friend2['name']}_start"]
                )
            
            # Start constraint
            if num_meetings > 0:
                first_friend = friends[0]
                travel_to_first = travel_times.get(('Golden Gate Park', first_friend['location']), 30)
                temp_problem.addConstraint(
                    lambda start: start >= current_time + travel_to_first,
                    [f"{first_friend['name']}_start"]
                )
            
            temp_solutions = temp_problem.getSolutions()
            if temp_solutions:
                best_solution = temp_solutions[0]
                max_meetings = num_meetings
                break
        
        solution = best_solution
    else:
        solution = solutions[0]
        max_meetings = len(friends)

    # Build itinerary
    itinerary = []
    
    if solution:
        # Create list of meetings with their start times
        meetings = []
        for friend in friends:
            if f"{friend['name']}_start" in solution:
                meetings.append({
                    'name': friend['name'],
                    'location': friend['location'],
                    'start': solution[f"{friend['name']}_start"],
                    'duration': friend['min_duration'],
                    'end': solution[f"{friend['name']}_start"] + friend['min_duration']
                })
        
        # Sort meetings by start time
        meetings.sort(key=lambda x: x['start'])
        
        # Add travel from Golden Gate Park to first meeting
        if meetings:
            first_meeting = meetings[0]
            travel_time = travel_times.get(('Golden Gate Park', first_meeting['location']), 30)
            itinerary.append({
                'action': 'travel',
                'location': first_meeting['location'],
                'person': '',
                'start_time': minutes_to_time(start_time_minutes),
                'end_time': minutes_to_time(first_meeting['start'])
            })
        
        # Add meetings
        for i, meeting in enumerate(meetings):
            itinerary.append({
                'action': 'meet',
                'location': meeting['location'],
                'person': meeting['name'],
                'start_time': minutes_to_time(meeting['start']),
                'end_time': minutes_to_time(meeting['end'])
            })
            
            # Add travel to next meeting if there is one
            if i < len(meetings) - 1:
                next_meeting = meetings[i + 1]
                travel_time = travel_times.get((meeting['location'], next_meeting['location']), 30)
                itinerary.append({
                    'action': 'travel',
                    'location': next_meeting['location'],
                    'person': '',
                    'start_time': minutes_to_time(meeting['end']),
                    'end_time': minutes_to_time(next_meeting['start'])
                })
    
    # Output result
    result = {
        "itinerary": itinerary
    }
    
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()