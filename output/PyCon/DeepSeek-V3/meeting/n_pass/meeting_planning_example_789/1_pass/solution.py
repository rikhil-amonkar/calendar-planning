import constraint
from datetime import datetime, timedelta
import json

def time_to_minutes(time_str):
    """Convert time string (H:MM) to minutes since midnight"""
    dt = datetime.strptime(time_str, "%H:%M")
    return dt.hour * 60 + dt.minute

def minutes_to_time(minutes):
    """Convert minutes since midnight to time string (H:MM)"""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    # Travel times dictionary (in minutes)
    travel_times = {
        ('Union Square', 'Russian Hill'): 13,
        ('Union Square', 'Alamo Square'): 15,
        ('Union Square', 'Haight-Ashbury'): 18,
        ('Union Square', 'Marina District'): 18,
        ('Union Square', 'Bayview'): 15,
        ('Union Square', 'Chinatown'): 7,
        ('Union Square', 'Presidio'): 24,
        ('Union Square', 'Sunset District'): 27,
        ('Russian Hill', 'Union Square'): 10,
        ('Russian Hill', 'Alamo Square'): 15,
        ('Russian Hill', 'Haight-Ashbury'): 17,
        ('Russian Hill', 'Marina District'): 7,
        ('Russian Hill', 'Bayview'): 23,
        ('Russian Hill', 'Chinatown'): 9,
        ('Russian Hill', 'Presidio'): 14,
        ('Russian Hill', 'Sunset District'): 23,
        ('Alamo Square', 'Union Square'): 14,
        ('Alamo Square', 'Russian Hill'): 13,
        ('Alamo Square', 'Haight-Ashbury'): 5,
        ('Alamo Square', 'Marina District'): 15,
        ('Alamo Square', 'Bayview'): 16,
        ('Alamo Square', 'Chinatown'): 15,
        ('Alamo Square', 'Presidio'): 17,
        ('Alamo Square', 'Sunset District'): 16,
        ('Haight-Ashbury', 'Union Square'): 19,
        ('Haight-Ashbury', 'Russian Hill'): 17,
        ('Haight-Ashbury', 'Alamo Square'): 5,
        ('Haight-Ashbury', 'Marina District'): 17,
        ('Haight-Ashbury', 'Bayview'): 18,
        ('Haight-Ashbury', 'Chinatown'): 19,
        ('Haight-Ashbury', 'Presidio'): 15,
        ('Haight-Ashbury', 'Sunset District'): 15,
        ('Marina District', 'Union Square'): 16,
        ('Marina District', 'Russian Hill'): 8,
        ('Marina District', 'Alamo Square'): 15,
        ('Marina District', 'Haight-Ashbury'): 16,
        ('Marina District', 'Bayview'): 27,
        ('Marina District', 'Chinatown'): 15,
        ('Marina District', 'Presidio'): 10,
        ('Marina District', 'Sunset District'): 19,
        ('Bayview', 'Union Square'): 18,
        ('Bayview', 'Russian Hill'): 23,
        ('Bayview', 'Alamo Square'): 16,
        ('Bayview', 'Haight-Ashbury'): 19,
        ('Bayview', 'Marina District'): 27,
        ('Bayview', 'Chinatown'): 19,
        ('Bayview', 'Presidio'): 32,
        ('Bayview', 'Sunset District'): 23,
        ('Chinatown', 'Union Square'): 7,
        ('Chinatown', 'Russian Hill'): 7,
        ('Chinatown', 'Alamo Square'): 17,
        ('Chinatown', 'Haight-Ashbury'): 19,
        ('Chinatown', 'Marina District'): 12,
        ('Chinatown', 'Bayview'): 20,
        ('Chinatown', 'Presidio'): 19,
        ('Chinatown', 'Sunset District'): 29,
        ('Presidio', 'Union Square'): 22,
        ('Presidio', 'Russian Hill'): 14,
        ('Presidio', 'Alamo Square'): 19,
        ('Presidio', 'Haight-Ashbury'): 15,
        ('Presidio', 'Marina District'): 11,
        ('Presidio', 'Bayview'): 31,
        ('Presidio', 'Chinatown'): 21,
        ('Presidio', 'Sunset District'): 15,
        ('Sunset District', 'Union Square'): 30,
        ('Sunset District', 'Russian Hill'): 24,
        ('Sunset District', 'Alamo Square'): 17,
        ('Sunset District', 'Haight-Ashbury'): 15,
        ('Sunset District', 'Marina District'): 21,
        ('Sunset District', 'Bayview'): 22,
        ('Sunset District', 'Chinatown'): 30,
        ('Sunset District', 'Presidio'): 16,
    }
    
    # Friend constraints
    friends = [
        {
            'name': 'Betty',
            'location': 'Russian Hill',
            'available_start': '7:00',
            'available_end': '16:45',
            'min_duration': 105
        },
        {
            'name': 'Melissa',
            'location': 'Alamo Square',
            'available_start': '9:30',
            'available_end': '17:15',
            'min_duration': 105
        },
        {
            'name': 'Joshua',
            'location': 'Haight-Ashbury',
            'available_start': '12:15',
            'available_end': '19:00',
            'min_duration': 90
        },
        {
            'name': 'Jeffrey',
            'location': 'Marina District',
            'available_start': '12:15',
            'available_end': '18:00',
            'min_duration': 45
        },
        {
            'name': 'James',
            'location': 'Bayview',
            'available_start': '7:30',
            'available_end': '20:00',
            'min_duration': 90
        },
        {
            'name': 'Anthony',
            'location': 'Chinatown',
            'available_start': '11:45',
            'available_end': '13:30',
            'min_duration': 75
        },
        {
            'name': 'Timothy',
            'location': 'Presidio',
            'available_start': '12:30',
            'available_end': '14:45',
            'min_duration': 90
        },
        {
            'name': 'Emily',
            'location': 'Sunset District',
            'available_start': '19:30',
            'available_end': '21:30',
            'min_duration': 120
        }
    ]
    
    # Convert all times to minutes
    start_time_min = time_to_minutes('9:00')  # Starting at Union Square
    
    # Create problem
    problem = constraint.Problem()
    
    # Variables: start time for each meeting (in minutes since midnight)
    meeting_vars = []
    for friend in friends:
        var_name = f"{friend['name']}_start"
        available_start = time_to_minutes(friend['available_start'])
        available_end = time_to_minutes(friend['available_end'])
        
        # Meeting must start after available start and end before available end
        problem.addVariable(var_name, range(available_start, available_end - friend['min_duration'] + 1))
        meeting_vars.append(var_name)
    
    # Order constraints and travel time constraints
    for i in range(len(friends)):
        for j in range(i + 1, len(friends)):
            friend_i = friends[i]
            friend_j = friends[j]
            
            # If we meet friend_i before friend_j
            def constraint_before_i_j(friend_i_start, friend_j_start):
                travel_time = travel_times.get((friend_i['location'], friend_j['location']), 60)
                return friend_i_start + friend_i['min_duration'] + travel_time <= friend_j_start
            
            # If we meet friend_j before friend_i
            def constraint_before_j_i(friend_i_start, friend_j_start):
                travel_time = travel_times.get((friend_j['location'], friend_i['location']), 60)
                return friend_j_start + friend_j['min_duration'] + travel_time <= friend_i_start
            
            # Add both ordering possibilities
            problem.addConstraint(
                constraint_before_i_j, 
                [f"{friend_i['name']}_start", f"{friend_j['name']}_start"]
            )
            problem.addConstraint(
                constraint_before_j_i, 
                [f"{friend_i['name']}_start", f"{friend_j['name']}_start"]
            )
    
    # First meeting must be reachable from starting point
    for friend in friends:
        def constraint_first_meeting(start_time):
            travel_time = travel_times.get(('Union Square', friend['location']), 60)
            return start_time_min + travel_time <= start_time
        
        problem.addConstraint(
            constraint_first_meeting,
            [f"{friend['name']}_start"]
        )
    
    # Objective: maximize number of meetings
    solutions = problem.getSolutions()
    
    if not solutions:
        # Fallback: try to find a solution with fewer meetings
        best_solution = None
        best_meetings = 0
        
        # Try all subsets of friends
        from itertools import combinations
        for num_meetings in range(len(friends), 0, -1):
            for friend_subset in combinations(friends, num_meetings):
                problem_subset = constraint.Problem()
                meeting_vars_subset = []
                
                for friend in friend_subset:
                    var_name = f"{friend['name']}_start"
                    available_start = time_to_minutes(friend['available_start'])
                    available_end = time_to_minutes(friend['available_end'])
                    
                    problem_subset.addVariable(var_name, range(available_start, available_end - friend['min_duration'] + 1))
                    meeting_vars_subset.append(var_name)
                
                # Add constraints for the subset
                for i in range(len(friend_subset)):
                    for j in range(i + 1, len(friend_subset)):
                        friend_i = friend_subset[i]
                        friend_j = friend_subset[j]
                        
                        def constraint_before_i_j_subset(friend_i_start, friend_j_start):
                            travel_time = travel_times.get((friend_i['location'], friend_j['location']), 60)
                            return friend_i_start + friend_i['min_duration'] + travel_time <= friend_j_start
                        
                        def constraint_before_j_i_subset(friend_i_start, friend_j_start):
                            travel_time = travel_times.get((friend_j['location'], friend_i['location']), 60)
                            return friend_j_start + friend_j['min_duration'] + travel_time <= friend_i_start
                        
                        problem_subset.addConstraint(
                            constraint_before_i_j_subset, 
                            [f"{friend_i['name']}_start", f"{friend_j['name']}_start"]
                        )
                        problem_subset.addConstraint(
                            constraint_before_j_i_subset, 
                            [f"{friend_i['name']}_start", f"{friend_j['name']}_start"]
                        )
                
                # First meeting constraint
                for friend in friend_subset:
                    def constraint_first_meeting_subset(start_time):
                        travel_time = travel_times.get(('Union Square', friend['location']), 60)
                        return start_time_min + travel_time <= start_time
                    
                    problem_subset.addConstraint(
                        constraint_first_meeting_subset,
                        [f"{friend['name']}_start"]
                    )
                
                solutions_subset = problem_subset.getSolutions()
                if solutions_subset:
                    best_solution = solutions_subset[0]
                    best_meetings = num_meetings
                    break
            
            if best_solution:
                break
        
        if best_solution:
            solution = best_solution
        else:
            # If no solution found, create empty itinerary
            solution = {}
    else:
        # Use first solution found
        solution = solutions[0]
    
    # Build itinerary
    itinerary = []
    
    # Create meeting events from solution
    meetings = []
    for friend in friends:
        start_var = f"{friend['name']}_start"
        if start_var in solution:
            start_time = solution[start_var]
            end_time = start_time + friend['min_duration']
            meetings.append({
                'person': friend['name'],
                'location': friend['location'],
                'start_time': start_time,
                'end_time': end_time
            })
    
    # Sort meetings by start time
    meetings.sort(key=lambda x: x['start_time'])
    
    # Add travel from starting point to first meeting
    if meetings:
        first_meeting = meetings[0]
        travel_start = start_time_min
        travel_end = first_meeting['start_time']
        itinerary.append({
            'action': 'travel',
            'location': first_meeting['location'],
            'person': '',
            'start_time': minutes_to_time(travel_start),
            'end_time': minutes_to_time(travel_end)
        })
    
    # Add meetings and travel between them
    for i, meeting in enumerate(meetings):
        # Add the meeting
        itinerary.append({
            'action': 'meet',
            'location': meeting['location'],
            'person': meeting['person'],
            'start_time': minutes_to_time(meeting['start_time']),
            'end_time': minutes_to_time(meeting['end_time'])
        })
        
        # Add travel to next meeting if there is one
        if i < len(meetings) - 1:
            next_meeting = meetings[i + 1]
            travel_time = travel_times.get((meeting['location'], next_meeting['location']), 60)
            
            travel_start = meeting['end_time']
            travel_end = next_meeting['start_time']
            
            # Only add travel if there's actual travel time
            if travel_end > travel_start:
                itinerary.append({
                    'action': 'travel',
                    'location': next_meeting['location'],
                    'person': '',
                    'start_time': minutes_to_time(travel_start),
                    'end_time': minutes_to_time(travel_end)
                })
    
    # Output as JSON
    output = {
        "itinerary": itinerary
    }
    
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()