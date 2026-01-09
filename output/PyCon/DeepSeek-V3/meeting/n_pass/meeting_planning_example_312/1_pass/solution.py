import constraint
from datetime import datetime, timedelta
import json

def main():
    # Travel times in minutes between locations
    travel_times = {
        ('Richmond District', 'Sunset District'): 11,
        ('Richmond District', 'Haight-Ashbury'): 10,
        ('Richmond District', 'Mission District'): 20,
        ('Richmond District', 'Golden Gate Park'): 9,
        ('Sunset District', 'Richmond District'): 12,
        ('Sunset District', 'Haight-Ashbury'): 15,
        ('Sunset District', 'Mission District'): 24,
        ('Sunset District', 'Golden Gate Park'): 11,
        ('Haight-Ashbury', 'Richmond District'): 10,
        ('Haight-Ashbury', 'Sunset District'): 15,
        ('Haight-Ashbury', 'Mission District'): 11,
        ('Haight-Ashbury', 'Golden Gate Park'): 7,
        ('Mission District', 'Richmond District'): 20,
        ('Mission District', 'Sunset District'): 24,
        ('Mission District', 'Haight-Ashbury'): 12,
        ('Mission District', 'Golden Gate Park'): 17,
        ('Golden Gate Park', 'Richmond District'): 7,
        ('Golden Gate Park', 'Sunset District'): 10,
        ('Golden Gate Park', 'Haight-Ashbury'): 7,
        ('Golden Gate Park', 'Mission District'): 17
    }
    
    # Friend constraints
    friends = {
        'Sarah': {
            'location': 'Sunset District',
            'available_start': datetime.strptime('10:45', '%H:%M'),
            'available_end': datetime.strptime('19:00', '%H:%M'),
            'min_duration': 30  # minutes
        },
        'Richard': {
            'location': 'Haight-Ashbury',
            'available_start': datetime.strptime('11:45', '%H:%M'),
            'available_end': datetime.strptime('15:45', '%H:%M'),
            'min_duration': 90
        },
        'Elizabeth': {
            'location': 'Mission District',
            'available_start': datetime.strptime('11:00', '%H:%M'),
            'available_end': datetime.strptime('17:15', '%H:%M'),
            'min_duration': 120
        },
        'Michelle': {
            'location': 'Golden Gate Park',
            'available_start': datetime.strptime('18:15', '%H:%M'),
            'available_end': datetime.strptime('20:45', '%H:%M'),
            'min_duration': 90
        }
    }
    
    # Start location and time
    start_location = 'Richmond District'
    start_time = datetime.strptime('9:00', '%H:%M')
    
    # Create problem
    problem = constraint.Problem()
    
    # Define variables for each friend: start time in minutes from 9:00
    max_time_minutes = 720  # 12 hours from 9:00 to 21:00
    
    for friend in friends:
        available_start_minutes = int((friends[friend]['available_start'] - start_time).total_seconds() / 60)
        available_end_minutes = int((friends[friend]['available_end'] - start_time).total_seconds() / 60)
        min_duration = friends[friend]['min_duration']
        
        # Start time must be within availability window minus duration
        problem.addVariable(f"{friend}_start", range(available_start_minutes, available_end_minutes - min_duration + 1))
        problem.addVariable(f"{friend}_duration", [min_duration])  # Fixed to minimum duration
    
    # Add constraint: meetings cannot overlap and must account for travel
    friend_names = list(friends.keys())
    
    def no_overlap_constraint(*args):
        # Extract start times and durations
        schedule = []
        for i, friend in enumerate(friend_names):
            start = args[i * 2]
            duration = args[i * 2 + 1]
            schedule.append((friend, start, start + duration))
        
        # Sort by start time
        schedule.sort(key=lambda x: x[1])
        
        # Check for overlaps and travel time
        for i in range(len(schedule) - 1):
            current_friend, current_start, current_end = schedule[i]
            next_friend, next_start, next_end = schedule[i + 1]
            
            # Current meeting must end before next meeting starts
            if current_end > next_start:
                return False
            
            # Add travel time between locations
            current_loc = friends[current_friend]['location']
            next_loc = friends[next_friend]['location']
            travel_time = travel_times.get((current_loc, next_loc), 30)  # Default 30 if not found
            
            # Travel time must be accounted for
            if current_end + travel_time > next_start:
                return False
        
        return True
    
    # Add the constraint
    variables = []
    for friend in friend_names:
        variables.append(f"{friend}_start")
        variables.append(f"{friend}_duration")
    
    problem.addConstraint(no_overlap_constraint, variables)
    
    # Try to maximize number of meetings (primary) and total meeting time (secondary)
    solutions = problem.getSolutions()
    
    if not solutions:
        # Fallback: try to find any valid schedule
        # Relax constraints by trying shorter durations if needed
        for friend in friends:
            problem.addVariable(f"{friend}_duration", range(friends[friend]['min_duration'], 
                                                          int((friends[friend]['available_end'] - friends[friend]['available_start']).total_seconds() / 60) + 1))
        
        solutions = problem.getSolutions()
    
    if solutions:
        # Find best solution (maximize number of meetings, then total duration)
        best_solution = None
        best_score = -1
        
        for solution in solutions:
            num_meetings = len([f for f in friend_names if f"{f}_start" in solution])
            total_duration = sum(solution.get(f"{f}_duration", 0) for f in friend_names)
            
            score = num_meetings * 1000 + total_duration  # Prioritize number of meetings
            
            if score > best_score:
                best_score = score
                best_solution = solution
        
        # Build itinerary
        itinerary = []
        
        # Create list of meetings with their times
        meetings = []
        for friend in friend_names:
            if f"{friend}_start" in best_solution:
                start_minutes = best_solution[f"{friend}_start"]
                duration = best_solution[f"{friend}_duration"]
                
                start_time_actual = start_time + timedelta(minutes=start_minutes)
                end_time_actual = start_time_actual + timedelta(minutes=duration)
                
                meetings.append({
                    'friend': friend,
                    'location': friends[friend]['location'],
                    'start': start_time_actual,
                    'end': end_time_actual
                })
        
        # Sort meetings by start time
        meetings.sort(key=lambda x: x['start'])
        
        # Add travel from start location to first meeting
        if meetings:
            first_meeting = meetings[0]
            travel_start = start_location
            travel_end = first_meeting['location']
            travel_duration = travel_times.get((travel_start, travel_end), 15)
            
            travel_start_time = first_meeting['start'] - timedelta(minutes=travel_duration)
            if travel_start_time > start_time:
                itinerary.append({
                    "action": "travel",
                    "location": travel_end,
                    "person": "",
                    "start_time": start_time.strftime('%H:%M'),
                    "end_time": travel_start_time.strftime('%H:%M')
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
                travel_start = meeting['location']
                travel_end = next_meeting['location']
                travel_duration = travel_times.get((travel_start, travel_end), 15)
                
                travel_start_time = meeting['end']
                travel_end_time = travel_start_time + timedelta(minutes=travel_duration)
                
                if travel_end_time <= next_meeting['start']:
                    itinerary.append({
                        "action": "travel",
                        "location": travel_end,
                        "person": "",
                        "start_time": travel_start_time.strftime('%H:%M'),
                        "end_time": travel_end_time.strftime('%H:%M')
                    })
        
        # Output result
        result = {
            "itinerary": itinerary
        }
        print(json.dumps(result, indent=2))
    else:
        # No solution found
        print(json.dumps({"itinerary": []}, indent=2))

if __name__ == "__main__":
    main()