import constraint
from datetime import datetime, timedelta
import json

def main():
    # Define locations
    locations = [
        "Sunset District", "Russian Hill", "The Castro", "Richmond District",
        "Marina District", "North Beach", "Union Square", "Golden Gate Park"
    ]
    
    # Travel time matrix (minutes)
    travel_times = {
        ("Sunset District", "Russian Hill"): 24,
        ("Sunset District", "The Castro"): 17,
        ("Sunset District", "Richmond District"): 12,
        ("Sunset District", "Marina District"): 21,
        ("Sunset District", "North Beach"): 29,
        ("Sunset District", "Union Square"): 30,
        ("Sunset District", "Golden Gate Park"): 11,
        ("Russian Hill", "Sunset District"): 23,
        ("Russian Hill", "The Castro"): 21,
        ("Russian Hill", "Richmond District"): 14,
        ("Russian Hill", "Marina District"): 7,
        ("Russian Hill", "North Beach"): 5,
        ("Russian Hill", "Union Square"): 11,
        ("Russian Hill", "Golden Gate Park"): 21,
        ("The Castro", "Sunset District"): 17,
        ("The Castro", "Russian Hill"): 18,
        ("The Castro", "Richmond District"): 16,
        ("The Castro", "Marina District"): 21,
        ("The Castro", "North Beach"): 20,
        ("The Castro", "Union Square"): 19,
        ("The Castro", "Golden Gate Park"): 11,
        ("Richmond District", "Sunset District"): 11,
        ("Richmond District", "Russian Hill"): 13,
        ("Richmond District", "The Castro"): 16,
        ("Richmond District", "Marina District"): 9,
        ("Richmond District", "North Beach"): 17,
        ("Richmond District", "Union Square"): 21,
        ("Richmond District", "Golden Gate Park"): 9,
        ("Marina District", "Sunset District"): 19,
        ("Marina District", "Russian Hill"): 8,
        ("Marina District", "The Castro"): 22,
        ("Marina District", "Richmond District"): 11,
        ("Marina District", "North Beach"): 11,
        ("Marina District", "Union Square"): 16,
        ("Marina District", "Golden Gate Park"): 18,
        ("North Beach", "Sunset District"): 27,
        ("North Beach", "Russian Hill"): 4,
        ("North Beach", "The Castro"): 22,
        ("North Beach", "Richmond District"): 18,
        ("North Beach", "Marina District"): 9,
        ("North Beach", "Union Square"): 7,
        ("North Beach", "Golden Gate Park"): 22,
        ("Union Square", "Sunset District"): 26,
        ("Union Square", "Russian Hill"): 13,
        ("Union Square", "The Castro"): 19,
        ("Union Square", "Richmond District"): 20,
        ("Union Square", "Marina District"): 18,
        ("Union Square", "North Beach"): 10,
        ("Union Square", "Golden Gate Park"): 22,
        ("Golden Gate Park", "Sunset District"): 10,
        ("Golden Gate Park", "Russian Hill"): 19,
        ("Golden Gate Park", "The Castro"): 13,
        ("Golden Gate Park", "Richmond District"): 7,
        ("Golden Gate Park", "Marina District"): 16,
        ("Golden Gate Park", "North Beach"): 24,
        ("Golden Gate Park", "Union Square"): 22,
    }
    
    # Friend constraints
    friends = {
        "Karen": {
            "location": "Russian Hill",
            "available_start": "20:45",  # 8:45 PM
            "available_end": "21:45",    # 9:45 PM
            "min_duration": 60
        },
        "Jessica": {
            "location": "The Castro",
            "available_start": "15:45",  # 3:45 PM
            "available_end": "19:30",    # 7:30 PM
            "min_duration": 60
        },
        "Matthew": {
            "location": "Richmond District",
            "available_start": "7:30",   # 7:30 AM
            "available_end": "15:15",    # 3:15 PM
            "min_duration": 15
        },
        "Michelle": {
            "location": "Marina District",
            "available_start": "10:30",  # 10:30 AM
            "available_end": "18:45",    # 6:45 PM
            "min_duration": 75
        },
        "Carol": {
            "location": "North Beach",
            "available_start": "12:00",  # 12:00 PM
            "available_end": "17:00",    # 5:00 PM
            "min_duration": 90
        },
        "Stephanie": {
            "location": "Union Square",
            "available_start": "10:45",  # 10:45 AM
            "available_end": "14:15",    # 2:15 PM
            "min_duration": 30
        },
        "Linda": {
            "location": "Golden Gate Park",
            "available_start": "10:45",  # 10:45 AM
            "available_end": "22:00",    # 10:00 PM
            "min_duration": 90
        }
    }
    
    # Convert time strings to minutes since 9:00
    def time_to_minutes(time_str):
        if ':' in time_str:
            hours, minutes = map(int, time_str.split(':'))
            return hours * 60 + minutes
        return 0
    
    def minutes_to_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours}:{mins:02d}"
    
    # Start time (9:00 AM)
    start_time_minutes = time_to_minutes("9:00")
    
    # Create problem
    problem = constraint.Problem()
    
    # Variables: start time for each friend (in minutes since 9:00)
    for friend in friends:
        available_start = time_to_minutes(friends[friend]["available_start"])
        available_end = time_to_minutes(friends[friend]["available_end"])
        min_duration = friends[friend]["min_duration"]
        
        # Adjust for start time constraint
        available_start = max(available_start, start_time_minutes)
        
        # Meeting must start and end within availability window
        max_start = available_end - min_duration
        if max_start >= available_start:
            problem.addVariable(f"{friend}_start", range(available_start, max_start + 1))
        else:
            problem.addVariable(f"{friend}_start", [])
    
    # Add travel time constraints
    friend_list = list(friends.keys())
    
    def travel_constraint(*starts):
        # Create list of meetings with their locations and times
        meetings = []
        for i, friend in enumerate(friend_list):
            if starts[i] is not None:
                meetings.append({
                    'friend': friend,
                    'location': friends[friend]['location'],
                    'start': starts[i],
                    'duration': friends[friend]['min_duration'],
                    'end': starts[i] + friends[friend]['min_duration']
                })
        
        # Sort meetings by start time
        meetings.sort(key=lambda x: x['start'])
        
        # Check travel times between consecutive meetings
        for i in range(len(meetings) - 1):
            current = meetings[i]
            next_meeting = meetings[i + 1]
            
            travel_key = (current['location'], next_meeting['location'])
            travel_time = travel_times.get(travel_key, 999)
            
            # Check if there's enough time to travel
            if current['end'] + travel_time > next_meeting['start']:
                return False
        
        return True
    
    # Add the constraint for all combinations
    if friend_list:
        problem.addConstraint(travel_constraint, [f"{friend}_start" for friend in friend_list])
    
    # Find solutions
    solutions = problem.getSolutions()
    
    if not solutions:
        # Fallback: try to meet as many friends as possible
        best_solution = None
        max_friends = 0
        
        for friend_count in range(len(friend_list), 0, -1):
            # Try all combinations of friends
            from itertools import combinations
            
            for friend_combo in combinations(friend_list, friend_count):
                sub_problem = constraint.Problem()
                
                for friend in friend_combo:
                    available_start = time_to_minutes(friends[friend]["available_start"])
                    available_end = time_to_minutes(friends[friend]["available_end"])
                    min_duration = friends[friend]["min_duration"]
                    
                    available_start = max(available_start, start_time_minutes)
                    max_start = available_end - min_duration
                    
                    if max_start >= available_start:
                        sub_problem.addVariable(f"{friend}_start", range(available_start, max_start + 1))
                    else:
                        break
                else:
                    # All friends in combo have valid time windows
                    if len(friend_combo) > 1:
                        sub_problem.addConstraint(travel_constraint, [f"{friend}_start" for friend in friend_combo])
                    
                    sub_solutions = sub_problem.getSolutions()
                    if sub_solutions:
                        best_solution = sub_solutions[0]
                        max_friends = friend_count
                        break
            
            if best_solution:
                break
        
        if not best_solution:
            # Last resort: just pick one friend
            for friend in friend_list:
                available_start = time_to_minutes(friends[friend]["available_start"])
                available_end = time_to_minutes(friends[friend]["available_end"])
                min_duration = friends[friend]["min_duration"]
                
                available_start = max(available_start, start_time_minutes)
                max_start = available_end - min_duration
                
                if max_start >= available_start:
                    best_solution = {f"{friend}_start": available_start}
                    break
        
        solution = best_solution
    else:
        solution = solutions[0]
    
    # Build itinerary
    itinerary = []
    
    # Create list of meetings
    meetings = []
    for friend in friend_list:
        if f"{friend}_start" in solution:
            start_minutes = solution[f"{friend}_start"]
            duration = friends[friend]["min_duration"]
            end_minutes = start_minutes + duration
            
            meetings.append({
                'friend': friend,
                'location': friends[friend]['location'],
                'start': start_minutes,
                'end': end_minutes
            })
    
    # Sort by start time
    meetings.sort(key=lambda x: x['start'])
    
    # Add meetings to itinerary
    for meeting in meetings:
        itinerary.append({
            "action": "meet",
            "location": meeting['location'],
            "person": meeting['friend'],
            "start_time": minutes_to_time(meeting['start']),
            "end_time": minutes_to_time(meeting['end'])
        })
    
    # Output result
    result = {
        "itinerary": itinerary
    }
    
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()