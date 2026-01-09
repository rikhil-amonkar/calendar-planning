import constraint
import json
from datetime import datetime, timedelta

def main():
    # Define locations
    locations = ['Richmond', 'Marina', 'Chinatown', 'Financial', 'Bayview', 'Union Square']
    
    # Travel times in minutes (matrix)
    travel_times = {
        ('Richmond', 'Marina'): 9,
        ('Richmond', 'Chinatown'): 20,
        ('Richmond', 'Financial'): 22,
        ('Richmond', 'Bayview'): 26,
        ('Richmond', 'Union Square'): 21,
        ('Marina', 'Richmond'): 11,
        ('Marina', 'Chinatown'): 16,
        ('Marina', 'Financial'): 17,
        ('Marina', 'Bayview'): 27,
        ('Marina', 'Union Square'): 16,
        ('Chinatown', 'Richmond'): 20,
        ('Chinatown', 'Marina'): 12,
        ('Chinatown', 'Financial'): 5,
        ('Chinatown', 'Bayview'): 22,
        ('Chinatown', 'Union Square'): 7,
        ('Financial', 'Richmond'): 21,
        ('Financial', 'Marina'): 15,
        ('Financial', 'Chinatown'): 5,
        ('Financial', 'Bayview'): 19,
        ('Financial', 'Union Square'): 9,
        ('Bayview', 'Richmond'): 25,
        ('Bayview', 'Marina'): 25,
        ('Bayview', 'Chinatown'): 18,
        ('Bayview', 'Financial'): 19,
        ('Bayview', 'Union Square'): 17,
        ('Union Square', 'Richmond'): 20,
        ('Union Square', 'Marina'): 18,
        ('Union Square', 'Chinatown'): 7,
        ('Union Square', 'Financial'): 9,
        ('Union Square', 'Bayview'): 15
    }
    
    # Friend constraints
    friends = {
        'Kimberly': {
            'location': 'Marina',
            'available_start': datetime.strptime('13:15', '%H:%M'),
            'available_end': datetime.strptime('16:45', '%H:%M'),
            'min_duration': 15
        },
        'Robert': {
            'location': 'Chinatown',
            'available_start': datetime.strptime('12:15', '%H:%M'),
            'available_end': datetime.strptime('20:15', '%H:%M'),
            'min_duration': 15
        },
        'Rebecca': {
            'location': 'Financial',
            'available_start': datetime.strptime('13:15', '%H:%M'),
            'available_end': datetime.strptime('16:45', '%H:%M'),
            'min_duration': 75
        },
        'Margaret': {
            'location': 'Bayview',
            'available_start': datetime.strptime('9:30', '%H:%M'),
            'available_end': datetime.strptime('13:30', '%H:%M'),
            'min_duration': 30
        },
        'Kenneth': {
            'location': 'Union Square',
            'available_start': datetime.strptime('19:30', '%H:%M'),
            'available_end': datetime.strptime('21:15', '%H:%M'),
            'min_duration': 75
        }
    }
    
    # Start time
    start_time = datetime.strptime('9:00', '%H:%M')
    current_location = 'Richmond'
    
    # Create problem
    problem = constraint.Problem()
    
    # Define variables for each friend: start_time (in minutes from 9:00), duration
    time_vars = {}
    for friend in friends:
        available_start_min = int((friends[friend]['available_start'] - start_time).total_seconds() / 60)
        available_end_min = int((friends[friend]['available_end'] - start_time).total_seconds() / 60)
        min_duration = friends[friend]['min_duration']
        
        # Start time can be from available_start to available_end - min_duration
        problem.addVariable(f"{friend}_start", range(available_start_min, available_end_min - min_duration + 1))
        # Duration is at least min_duration, up to the full available time
        problem.addVariable(f"{friend}_duration", range(min_duration, available_end_min - available_start_min + 1))
    
    # Add constraints to ensure meetings don't overlap and account for travel
    friend_list = list(friends.keys())
    
    for i in range(len(friend_list)):
        for j in range(i + 1, len(friend_list)):
            friend1 = friend_list[i]
            friend2 = friend_list[j]
            loc1 = friends[friend1]['location']
            loc2 = friends[friend2]['location']
            
            def no_overlap_with_travel(f1_start, f1_dur, f2_start, f2_dur, loc1=loc1, loc2=loc2):
                f1_end = f1_start + f1_dur
                f2_end = f2_start + f2_dur
                
                # If friend1 before friend2
                if f1_end + travel_times.get((loc1, loc2), 30) <= f2_start:
                    return True
                # If friend2 before friend1  
                if f2_end + travel_times.get((loc2, loc1), 30) <= f1_start:
                    return True
                return False
            
            problem.addConstraint(
                no_overlap_with_travel,
                [f"{friend1}_start", f"{friend1}_duration", f"{friend2}_start", f"{friend2}_duration"]
            )
    
    # Add constraint for starting from Richmond
    first_friend = friend_list[0]
    
    def can_reach_first(f_start, loc=current_location, first_loc=friends[first_friend]['location']):
        travel_time = travel_times.get((loc, first_loc), 30)
        return f_start >= travel_time
    
    problem.addConstraint(can_reach_first, [f"{first_friend}_start"])
    
    # Objective: maximize total meeting time
    def objective(*args):
        total_time = 0
        for i, friend in enumerate(friend_list):
            total_time += args[i * 2 + 1]  # duration is at odd indices
        return total_time
    
    # Find solution
    solutions = problem.getSolutions()
    
    if not solutions:
        # Fallback: try to meet as many friends as possible with minimum duration
        best_solution = None
        best_score = -1
        
        for friend in friend_list:
            # Try meeting just this one friend
            single_friend_problem = constraint.Problem()
            
            available_start_min = int((friends[friend]['available_start'] - start_time).total_seconds() / 60)
            available_end_min = int((friends[friend]['available_end'] - start_time).total_seconds() / 60)
            min_duration = friends[friend]['min_duration']
            
            travel_time = travel_times.get((current_location, friends[friend]['location']), 30)
            
            if available_start_min + min_duration <= available_end_min and available_start_min >= travel_time:
                if min_duration > best_score:
                    best_score = min_duration
                    best_solution = {
                        f"{friend}_start": max(available_start_min, travel_time),
                        f"{friend}_duration": min_duration
                    }
        
        if best_solution:
            solution = best_solution
        else:
            # No meetings possible
            solution = {}
    else:
        # Find solution with maximum total meeting time
        best_solution = None
        best_score = -1
        
        for sol in solutions:
            score = objective(*sol.values())
            if score > best_score:
                best_score = score
                best_solution = sol
        
        solution = best_solution
    
    # Build itinerary
    itinerary = []
    
    if solution:
        # Create list of meetings with their times
        meetings = []
        for friend in friend_list:
            if f"{friend}_start" in solution:
                start_min = solution[f"{friend}_start"]
                duration = solution[f"{friend}_duration"]
                start_time_actual = start_time + timedelta(minutes=start_min)
                end_time_actual = start_time + timedelta(minutes=start_min + duration)
                
                meetings.append({
                    'friend': friend,
                    'location': friends[friend]['location'],
                    'start': start_time_actual,
                    'end': end_time_actual
                })
        
        # Sort meetings by start time
        meetings.sort(key=lambda x: x['start'])
        
        # Add travel from starting point to first meeting
        if meetings:
            first_meeting = meetings[0]
            travel_start = start_time
            travel_end = first_meeting['start']
            if travel_end > travel_start:
                itinerary.append({
                    "action": "travel",
                    "location": first_meeting['location'],
                    "person": "",
                    "start_time": travel_start.strftime('%H:%M'),
                    "end_time": travel_end.strftime('%H:%M')
                })
        
        # Add meetings and travel between them
        for i, meeting in enumerate(meetings):
            # Add the meeting
            itinerary.append({
                "action": "meet",
                "location": meeting['location'],
                "person": meeting['friend'],
                "start_time": meeting['start'].strftime('%H:%M'),
                "end_time": meeting['end'].strftime('%H:%M')
            })
            
            # Add travel to next meeting if there is one
            if i < len(meetings) - 1:
                next_meeting = meetings[i + 1]
                travel_time_needed = travel_times.get(
                    (meeting['location'], next_meeting['location']), 30
                )
                
                travel_start = meeting['end']
                travel_end = next_meeting['start']
                
                # Only add travel if there's actual travel time
                if travel_end > travel_start:
                    itinerary.append({
                        "action": "travel",
                        "location": next_meeting['location'],
                        "person": "",
                        "start_time": travel_start.strftime('%H:%M'),
                        "end_time": travel_end.strftime('%H:%M')
                    })
    
    # Output as JSON
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()