import constraint
from datetime import datetime, timedelta
import json

def main():
    # Travel times in minutes between locations
    travel_times = {
        ('Nob Hill', 'Richmond District'): 14,
        ('Nob Hill', 'Financial District'): 9,
        ('Nob Hill', 'North Beach'): 8,
        ('Nob Hill', 'The Castro'): 17,
        ('Nob Hill', 'Golden Gate Park'): 17,
        ('Richmond District', 'Nob Hill'): 17,
        ('Richmond District', 'Financial District'): 22,
        ('Richmond District', 'North Beach'): 17,
        ('Richmond District', 'The Castro'): 16,
        ('Richmond District', 'Golden Gate Park'): 9,
        ('Financial District', 'Nob Hill'): 8,
        ('Financial District', 'Richmond District'): 21,
        ('Financial District', 'North Beach'): 7,
        ('Financial District', 'The Castro'): 23,
        ('Financial District', 'Golden Gate Park'): 23,
        ('North Beach', 'Nob Hill'): 7,
        ('North Beach', 'Richmond District'): 18,
        ('North Beach', 'Financial District'): 8,
        ('North Beach', 'The Castro'): 22,
        ('North Beach', 'Golden Gate Park'): 22,
        ('The Castro', 'Nob Hill'): 16,
        ('The Castro', 'Richmond District'): 16,
        ('The Castro', 'Financial District'): 20,
        ('The Castro', 'North Beach'): 20,
        ('The Castro', 'Golden Gate Park'): 11,
        ('Golden Gate Park', 'Nob Hill'): 20,
        ('Golden Gate Park', 'Richmond District'): 7,
        ('Golden Gate Park', 'Financial District'): 26,
        ('Golden Gate Park', 'North Beach'): 24,
        ('Golden Gate Park', 'The Castro'): 13
    }

    # Friend constraints
    friends = {
        'Emily': {
            'location': 'Richmond District',
            'available_start': datetime.strptime('19:00', '%H:%M'),
            'available_end': datetime.strptime('21:00', '%H:%M'),
            'min_duration': 15
        },
        'Margaret': {
            'location': 'Financial District',
            'available_start': datetime.strptime('16:30', '%H:%M'),
            'available_end': datetime.strptime('20:15', '%H:%M'),
            'min_duration': 75
        },
        'Ronald': {
            'location': 'North Beach',
            'available_start': datetime.strptime('18:30', '%H:%M'),
            'available_end': datetime.strptime('19:30', '%H:%M'),
            'min_duration': 45
        },
        'Deborah': {
            'location': 'The Castro',
            'available_start': datetime.strptime('13:45', '%H:%M'),
            'available_end': datetime.strptime('21:15', '%H:%M'),
            'min_duration': 90
        },
        'Jeffrey': {
            'location': 'Golden Gate Park',
            'available_start': datetime.strptime('11:15', '%H:%M'),
            'available_end': datetime.strptime('14:30', '%H:%M'),
            'min_duration': 120
        }
    }

    # Start at Nob Hill at 9:00 AM
    start_time = datetime.strptime('9:00', '%H:%M')
    current_location = 'Nob Hill'
    current_time = start_time
    end_of_day = datetime.strptime('21:00', '%H:%M')

    problem = constraint.Problem()

    # Define variables for each friend: start time in minutes from 9:00
    friend_names = list(friends.keys())
    
    for friend in friend_names:
        available_start_minutes = int((friends[friend]['available_start'] - start_time).total_seconds() / 60)
        available_end_minutes = int((friends[friend]['available_end'] - start_time).total_seconds() / 60)
        problem.addVariable(f"{friend}_start", range(available_start_minutes, available_end_minutes - friends[friend]['min_duration'] + 1))
        problem.addVariable(f"{friend}_duration", [friends[friend]['min_duration']])

    # Helper function to convert minutes to time string
    def minutes_to_time(minutes):
        time_obj = start_time + timedelta(minutes=minutes)
        return time_obj.strftime('%H:%M')

    # Find a feasible schedule
    def schedule_constraint(*args):
        # Create a list of meetings with their details
        meetings = []
        for i, friend in enumerate(friend_names):
            start_idx = i * 2
            duration_idx = i * 2 + 1
            meetings.append({
                'friend': friend,
                'start': args[start_idx],
                'duration': args[duration_idx],
                'location': friends[friend]['location'],
                'end': args[start_idx] + args[duration_idx]
            })
        
        # Sort meetings by start time
        meetings.sort(key=lambda x: x['start'])
        
        # Check if meetings fit in the day and account for travel
        current_pos = current_location
        current_time_minutes = 0
        
        for i, meeting in enumerate(meetings):
            # Travel time to meeting location
            if i == 0:
                travel_time = travel_times.get((current_pos, meeting['location']), 0)
            else:
                prev_meeting = meetings[i-1]
                travel_time = travel_times.get((prev_meeting['location'], meeting['location']), 0)
            
            # Check if we can reach the meeting on time
            if meeting['start'] < current_time_minutes + travel_time:
                return False
            
            # Update current position and time
            current_pos = meeting['location']
            current_time_minutes = meeting['end']
        
        return True

    # Add the constraint for all meetings
    all_vars = []
    for friend in friend_names:
        all_vars.append(f"{friend}_start")
        all_vars.append(f"{friend}_duration")
    
    problem.addConstraint(schedule_constraint, all_vars)

    # Find a solution
    solutions = problem.getSolutions()
    
    if not solutions:
        # If no solution found with all constraints, try to maximize number of meetings
        best_solution = None
        max_meetings = 0
        
        # Try different combinations of friends
        for num_friends in range(len(friend_names), 0, -1):
            from itertools import combinations
            for friend_combination in combinations(friend_names, num_friends):
                sub_problem = constraint.Problem()
                
                for friend in friend_combination:
                    available_start_minutes = int((friends[friend]['available_start'] - start_time).total_seconds() / 60)
                    available_end_minutes = int((friends[friend]['available_end'] - start_time).total_seconds() / 60)
                    sub_problem.addVariable(f"{friend}_start", range(available_start_minutes, available_end_minutes - friends[friend]['min_duration'] + 1))
                    sub_problem.addVariable(f"{friend}_duration", [friends[friend]['min_duration']])
                
                sub_vars = []
                for friend in friend_combination:
                    sub_vars.append(f"{friend}_start")
                    sub_vars.append(f"{friend}_duration")
                
                sub_problem.addConstraint(schedule_constraint, sub_vars)
                sub_solutions = sub_problem.getSolutions()
                
                if sub_solutions:
                    best_solution = sub_solutions[0]
                    max_meetings = num_friends
                    break
            
            if best_solution:
                break
        
        if not best_solution:
            # If still no solution, create a minimal schedule
            itinerary = []
            output = {"itinerary": itinerary}
            print(json.dumps(output))
            return
            
        solution = best_solution
        scheduled_friends = friend_combination if 'friend_combination' in locals() else friend_names
    else:
        solution = solutions[0]
        scheduled_friends = friend_names

    # Build the itinerary
    itinerary = []
    
    # Create meeting objects for the solution
    meetings = []
    for friend in scheduled_friends:
        start_time_minutes = solution[f"{friend}_start"]
        duration = solution[f"{friend}_duration"]
        meetings.append({
            'friend': friend,
            'location': friends[friend]['location'],
            'start': start_time_minutes,
            'duration': duration,
            'end': start_time_minutes + duration
        })
    
    # Sort meetings by start time
    meetings.sort(key=lambda x: x['start'])
    
    # Add meetings to itinerary
    for meeting in meetings:
        start_str = minutes_to_time(meeting['start'])
        end_str = minutes_to_time(meeting['end'])
        itinerary.append({
            "action": "meet",
            "location": meeting['location'],
            "person": meeting['friend'],
            "start_time": start_str,
            "end_time": end_str
        })

    output = {"itinerary": itinerary}
    print(json.dumps(output))

if __name__ == "__main__":
    main()