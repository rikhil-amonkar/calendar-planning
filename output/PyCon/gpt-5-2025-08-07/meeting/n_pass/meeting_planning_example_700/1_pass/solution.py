import constraint
from datetime import datetime, timedelta
import json

def main():
    # Define locations
    locations = [
        "Presidio", "Pacific Heights", "Golden Gate Park", "Fisherman's Wharf",
        "Marina District", "Alamo Square", "Sunset District", "Nob Hill", "North Beach"
    ]
    
    # Travel time matrix (minutes)
    travel_times = {
        ("Presidio", "Pacific Heights"): 11,
        ("Presidio", "Golden Gate Park"): 12,
        ("Presidio", "Fisherman's Wharf"): 19,
        ("Presidio", "Marina District"): 11,
        ("Presidio", "Alamo Square"): 19,
        ("Presidio", "Sunset District"): 15,
        ("Presidio", "Nob Hill"): 18,
        ("Presidio", "North Beach"): 18,
        ("Pacific Heights", "Presidio"): 11,
        ("Pacific Heights", "Golden Gate Park"): 15,
        ("Pacific Heights", "Fisherman's Wharf"): 13,
        ("Pacific Heights", "Marina District"): 6,
        ("Pacific Heights", "Alamo Square"): 10,
        ("Pacific Heights", "Sunset District"): 21,
        ("Pacific Heights", "Nob Hill"): 8,
        ("Pacific Heights", "North Beach"): 9,
        ("Golden Gate Park", "Presidio"): 11,
        ("Golden Gate Park", "Pacific Heights"): 16,
        ("Golden Gate Park", "Fisherman's Wharf"): 24,
        ("Golden Gate Park", "Marina District"): 16,
        ("Golden Gate Park", "Alamo Square"): 9,
        ("Golden Gate Park", "Sunset District"): 10,
        ("Golden Gate Park", "Nob Hill"): 20,
        ("Golden Gate Park", "North Beach"): 23,
        ("Fisherman's Wharf", "Presidio"): 17,
        ("Fisherman's Wharf", "Pacific Heights"): 12,
        ("Fisherman's Wharf", "Golden Gate Park"): 25,
        ("Fisherman's Wharf", "Marina District"): 9,
        ("Fisherman's Wharf", "Alamo Square"): 21,
        ("Fisherman's Wharf", "Sunset District"): 27,
        ("Fisherman's Wharf", "Nob Hill"): 11,
        ("Fisherman's Wharf", "North Beach"): 6,
        ("Marina District", "Presidio"): 10,
        ("Marina District", "Pacific Heights"): 7,
        ("Marina District", "Golden Gate Park"): 18,
        ("Marina District", "Fisherman's Wharf"): 10,
        ("Marina District", "Alamo Square"): 15,
        ("Marina District", "Sunset District"): 19,
        ("Marina District", "Nob Hill"): 12,
        ("Marina District", "North Beach"): 11,
        ("Alamo Square", "Presidio"): 17,
        ("Alamo Square", "Pacific Heights"): 10,
        ("Alamo Square", "Golden Gate Park"): 9,
        ("Alamo Square", "Fisherman's Wharf"): 19,
        ("Alamo Square", "Marina District"): 15,
        ("Alamo Square", "Sunset District"): 16,
        ("Alamo Square", "Nob Hill"): 11,
        ("Alamo Square", "North Beach"): 15,
        ("Sunset District", "Presidio"): 16,
        ("Sunset District", "Pacific Heights"): 21,
        ("Sunset District", "Golden Gate Park"): 11,
        ("Sunset District", "Fisherman's Wharf"): 29,
        ("Sunset District", "Marina District"): 21,
        ("Sunset District", "Alamo Square"): 17,
        ("Sunset District", "Nob Hill"): 27,
        ("Sunset District", "North Beach"): 28,
        ("Nob Hill", "Presidio"): 17,
        ("Nob Hill", "Pacific Heights"): 8,
        ("Nob Hill", "Golden Gate Park"): 17,
        ("Nob Hill", "Fisherman's Wharf"): 10,
        ("Nob Hill", "Marina District"): 11,
        ("Nob Hill", "Alamo Square"): 11,
        ("Nob Hill", "Sunset District"): 24,
        ("Nob Hill", "North Beach"): 8,
        ("North Beach", "Presidio"): 17,
        ("North Beach", "Pacific Heights"): 8,
        ("North Beach", "Golden Gate Park"): 22,
        ("North Beach", "Fisherman's Wharf"): 5,
        ("North Beach", "Marina District"): 9,
        ("North Beach", "Alamo Square"): 16,
        ("North Beach", "Sunset District"): 27,
        ("North Beach", "Nob Hill"): 7,
    }
    
    # Friend constraints
    friends = [
        {"name": "Kevin", "location": "Pacific Heights", "available_start": "7:15", "available_end": "8:45", "min_duration": 90},
        {"name": "Michelle", "location": "Golden Gate Park", "available_start": "20:00", "available_end": "21:00", "min_duration": 15},
        {"name": "Emily", "location": "Fisherman's Wharf", "available_start": "16:15", "available_end": "19:00", "min_duration": 30},
        {"name": "Mark", "location": "Marina District", "available_start": "18:15", "available_end": "19:45", "min_duration": 75},
        {"name": "Barbara", "location": "Alamo Square", "available_start": "17:00", "available_end": "19:00", "min_duration": 120},
        {"name": "Laura", "location": "Sunset District", "available_start": "19:00", "available_end": "21:15", "min_duration": 75},
        {"name": "Mary", "location": "Nob Hill", "available_start": "17:30", "available_end": "19:00", "min_duration": 45},
        {"name": "Helen", "location": "North Beach", "available_start": "11:00", "available_end": "12:15", "min_duration": 45}
    ]
    
    # Convert time strings to minutes since 9:00
    def time_to_minutes(time_str):
        if ':' in time_str:
            parts = time_str.split(':')
            hours = int(parts[0])
            minutes = int(parts[1])
            return hours * 60 + minutes
        return 0
    
    start_time_minutes = time_to_minutes("9:00")
    
    # Create problem
    problem = constraint.Problem()
    
    # Add variables for each friend (0 = not meeting, 1 = meeting)
    for friend in friends:
        problem.addVariable(f"{friend['name']}_meet", [0, 1])
    
    # Add variables for meeting start times (in minutes since 9:00)
    for friend in friends:
        available_start = time_to_minutes(friend['available_start'])
        available_end = time_to_minutes(friend['available_end'])
        # Adjust for our start time of 9:00
        available_start -= start_time_minutes
        available_end -= start_time_minutes
        
        # Generate possible start times (in 15-minute increments)
        possible_starts = []
        current = available_start
        while current + friend['min_duration'] <= available_end:
            possible_starts.append(current)
            current += 15  # 15-minute increments
        
        if possible_starts:
            problem.addVariable(f"{friend['name']}_start", possible_starts)
        else:
            problem.addVariable(f"{friend['name']}_start", [available_start])
    
    # Define objective function to maximize number of meetings
    def objective_function(*args):
        # Count number of meetings
        meeting_count = 0
        for i, friend in enumerate(friends):
            if args[i] == 1:  # If meeting this friend
                meeting_count += 1
        return meeting_count
    
    # Add constraint: if not meeting someone, their start time should be None
    for friend in friends:
        def meeting_constraint(meet_flag, start_time, friend=friend):
            if meet_flag == 0:
                return True  # No constraint if not meeting
            else:
                # Check if meeting duration fits in available window
                available_start = time_to_minutes(friend['available_start']) - start_time_minutes
                available_end = time_to_minutes(friend['available_end']) - start_time_minutes
                return start_time + friend['min_duration'] <= available_end
        
        problem.addConstraint(meeting_constraint, [f"{friend['name']}_meet", f"{friend['name']}_start"])
    
    # Add travel time constraints between consecutive meetings
    meeting_friends = [f for f in friends]
    
    for i in range(len(meeting_friends)):
        for j in range(i + 1, len(meeting_friends)):
            friend1 = meeting_friends[i]
            friend2 = meeting_friends[j]
            
            def travel_constraint(meet1, start1, meet2, start2, f1=friend1, f2=friend2):
                if meet1 == 0 or meet2 == 0:
                    return True  # No constraint if either meeting doesn't happen
                
                # Calculate travel time between locations
                travel_time = travel_times.get((f1['location'], f2['location']), 60)  # Default 60 min if not found
                
                # Check if there's enough time to travel between meetings
                end1 = start1 + f1['min_duration']
                if end1 + travel_time <= start2:
                    return True
                
                end2 = start2 + f2['min_duration']
                if end2 + travel_time <= start1:
                    return True
                
                return False
            
            problem.addConstraint(travel_constraint, [
                f"{friend1['name']}_meet", f"{friend1['name']}_start",
                f"{friend2['name']}_meet", f"{friend2['name']}_start"
            ])
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        # Fallback: try to meet as many as possible with relaxed constraints
        best_solution = {}
        for friend in friends:
            best_solution[f"{friend['name']}_meet"] = 0
            best_solution[f"{friend['name']}_start"] = 0
    else:
        # Find solution with maximum meetings
        best_solution = max(solutions, key=lambda s: sum(s[f"{friend['name']}_meet"] for friend in friends))
    
    # Build itinerary
    itinerary = []
    current_time = start_time_minutes
    
    # Sort meetings by start time
    meetings = []
    for friend in friends:
        if best_solution.get(f"{friend['name']}_meet", 0) == 1:
            start_time = best_solution.get(f"{friend['name']}_start", 0)
            meetings.append({
                "friend": friend,
                "start": start_time,
                "end": start_time + friend['min_duration']
            })
    
    # Sort by start time
    meetings.sort(key=lambda x: x['start'])
    
    # Add travel from Presidio to first meeting
    if meetings:
        first_meeting = meetings[0]
        travel_to_first = travel_times.get(("Presidio", first_meeting['friend']['location']), 30)
        
        # Add travel action if needed
        if travel_to_first > 0:
            travel_start = current_time
            travel_end = current_time + travel_to_first
            itinerary.append({
                "action": "travel",
                "from_location": "Presidio",
                "to_location": first_meeting['friend']['location'],
                "start_time": format_time(travel_start + start_time_minutes),
                "end_time": format_time(travel_end + start_time_minutes)
            })
            current_time = travel_end
    
    # Add meetings
    for i, meeting in enumerate(meetings):
        # Add meeting
        itinerary.append({
            "action": "meet",
            "location": meeting['friend']['location'],
            "person": meeting['friend']['name'],
            "start_time": format_time(meeting['start'] + start_time_minutes),
            "end_time": format_time(meeting['end'] + start_time_minutes)
        })
        current_time = meeting['end']
        
        # Add travel to next meeting if exists
        if i < len(meetings) - 1:
            next_meeting = meetings[i + 1]
            travel_time = travel_times.get((meeting['friend']['location'], next_meeting['friend']['location']), 30)
            
            if travel_time > 0:
                travel_start = current_time
                travel_end = current_time + travel_time
                itinerary.append({
                    "action": "travel",
                    "from_location": meeting['friend']['location'],
                    "to_location": next_meeting['friend']['location'],
                    "start_time": format_time(travel_start + start_time_minutes),
                    "end_time": format_time(travel_end + start_time_minutes)
                })
                current_time = travel_end
    
    # Filter to only include meeting actions in final output
    meeting_itinerary = [item for item in itinerary if item["action"] == "meet"]
    
    # Output as JSON
    result = {
        "itinerary": meeting_itinerary
    }
    
    print(json.dumps(result, indent=2))

def format_time(minutes_since_midnight):
    """Convert minutes since midnight to time string in format 'H:MM' or 'HH:MM'"""
    hours = minutes_since_midnight // 60
    minutes = minutes_since_midnight % 60
    return f"{hours}:{minutes:02d}"

if __name__ == "__main__":
    main()