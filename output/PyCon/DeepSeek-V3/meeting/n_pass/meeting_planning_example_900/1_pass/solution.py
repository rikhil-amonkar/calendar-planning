import constraint
from datetime import datetime, timedelta
import json

def main():
    # Define all locations
    locations = [
        "Richmond District", "The Castro", "Nob Hill", "Marina District", 
        "Pacific Heights", "Haight-Ashbury", "Mission District", "Chinatown",
        "Russian Hill", "Alamo Square", "Bayview"
    ]
    
    # Travel time matrix (in minutes)
    travel_times = {
        ("Richmond District", "The Castro"): 16,
        ("Richmond District", "Nob Hill"): 17,
        ("Richmond District", "Marina District"): 9,
        ("Richmond District", "Pacific Heights"): 10,
        ("Richmond District", "Haight-Ashbury"): 10,
        ("Richmond District", "Mission District"): 20,
        ("Richmond District", "Chinatown"): 20,
        ("Richmond District", "Russian Hill"): 13,
        ("Richmond District", "Alamo Square"): 13,
        ("Richmond District", "Bayview"): 27,
        ("The Castro", "Richmond District"): 16,
        ("The Castro", "Nob Hill"): 16,
        ("The Castro", "Marina District"): 21,
        ("The Castro", "Pacific Heights"): 16,
        ("The Castro", "Haight-Ashbury"): 6,
        ("The Castro", "Mission District"): 7,
        ("The Castro", "Chinatown"): 22,
        ("The Castro", "Russian Hill"): 18,
        ("The Castro", "Alamo Square"): 8,
        ("The Castro", "Bayview"): 19,
        ("Nob Hill", "Richmond District"): 14,
        ("Nob Hill", "The Castro"): 17,
        ("Nob Hill", "Marina District"): 11,
        ("Nob Hill", "Pacific Heights"): 8,
        ("Nob Hill", "Haight-Ashbury"): 13,
        ("Nob Hill", "Mission District"): 13,
        ("Nob Hill", "Chinatown"): 6,
        ("Nob Hill", "Russian Hill"): 5,
        ("Nob Hill", "Alamo Square"): 11,
        ("Nob Hill", "Bayview"): 19,
        ("Marina District", "Richmond District"): 11,
        ("Marina District", "The Castro"): 22,
        ("Marina District", "Nob Hill"): 12,
        ("Marina District", "Pacific Heights"): 7,
        ("Marina District", "Haight-Ashbury"): 16,
        ("Marina District", "Mission District"): 20,
        ("Marina District", "Chinatown"): 15,
        ("Marina District", "Russian Hill"): 8,
        ("Marina District", "Alamo Square"): 15,
        ("Marina District", "Bayview"): 27,
        ("Pacific Heights", "Richmond District"): 12,
        ("Pacific Heights", "The Castro"): 16,
        ("Pacific Heights", "Nob Hill"): 8,
        ("Pacific Heights", "Marina District"): 6,
        ("Pacific Heights", "Haight-Ashbury"): 11,
        ("Pacific Heights", "Mission District"): 15,
        ("Pacific Heights", "Chinatown"): 11,
        ("Pacific Heights", "Russian Hill"): 7,
        ("Pacific Heights", "Alamo Square"): 10,
        ("Pacific Heights", "Bayview"): 22,
        ("Haight-Ashbury", "Richmond District"): 10,
        ("Haight-Ashbury", "The Castro"): 6,
        ("Haight-Ashbury", "Nob Hill"): 15,
        ("Haight-Ashbury", "Marina District"): 17,
        ("Haight-Ashbury", "Pacific Heights"): 12,
        ("Haight-Ashbury", "Mission District"): 11,
        ("Haight-Ashbury", "Chinatown"): 19,
        ("Haight-Ashbury", "Russian Hill"): 17,
        ("Haight-Ashbury", "Alamo Square"): 5,
        ("Haight-Ashbury", "Bayview"): 18,
        ("Mission District", "Richmond District"): 20,
        ("Mission District", "The Castro"): 7,
        ("Mission District", "Nob Hill"): 12,
        ("Mission District", "Marina District"): 19,
        ("Mission District", "Pacific Heights"): 16,
        ("Mission District", "Haight-Ashbury"): 12,
        ("Mission District", "Chinatown"): 16,
        ("Mission District", "Russian Hill"): 15,
        ("Mission District", "Alamo Square"): 11,
        ("Mission District", "Bayview"): 14,
        ("Chinatown", "Richmond District"): 20,
        ("Chinatown", "The Castro"): 22,
        ("Chinatown", "Nob Hill"): 9,
        ("Chinatown", "Marina District"): 12,
        ("Chinatown", "Pacific Heights"): 10,
        ("Chinatown", "Haight-Ashbury"): 19,
        ("Chinatown", "Mission District"): 17,
        ("Chinatown", "Russian Hill"): 7,
        ("Chinatown", "Alamo Square"): 17,
        ("Chinatown", "Bayview"): 20,
        ("Russian Hill", "Richmond District"): 14,
        ("Russian Hill", "The Castro"): 21,
        ("Russian Hill", "Nob Hill"): 5,
        ("Russian Hill", "Marina District"): 7,
        ("Russian Hill", "Pacific Heights"): 7,
        ("Russian Hill", "Haight-Ashbury"): 17,
        ("Russian Hill", "Mission District"): 16,
        ("Russian Hill", "Chinatown"): 9,
        ("Russian Hill", "Alamo Square"): 15,
        ("Russian Hill", "Bayview"): 23,
        ("Alamo Square", "Richmond District"): 11,
        ("Alamo Square", "The Castro"): 8,
        ("Alamo Square", "Nob Hill"): 11,
        ("Alamo Square", "Marina District"): 15,
        ("Alamo Square", "Pacific Heights"): 10,
        ("Alamo Square", "Haight-Ashbury"): 5,
        ("Alamo Square", "Mission District"): 10,
        ("Alamo Square", "Chinatown"): 15,
        ("Alamo Square", "Russian Hill"): 13,
        ("Alamo Square", "Bayview"): 16,
        ("Bayview", "Richmond District"): 25,
        ("Bayview", "The Castro"): 19,
        ("Bayview", "Nob Hill"): 20,
        ("Bayview", "Marina District"): 27,
        ("Bayview", "Pacific Heights"): 23,
        ("Bayview", "Haight-Ashbury"): 19,
        ("Bayview", "Mission District"): 13,
        ("Bayview", "Chinatown"): 19,
        ("Bayview", "Russian Hill"): 23,
        ("Bayview", "Alamo Square"): 16,
    }
    
    # Friend constraints
    friends = [
        {"name": "Matthew", "location": "The Castro", "start": "16:30", "end": "20:00", "duration": 45},
        {"name": "Rebecca", "location": "Nob Hill", "start": "15:15", "end": "19:15", "duration": 105},
        {"name": "Brian", "location": "Marina District", "start": "14:15", "end": "22:00", "duration": 30},
        {"name": "Emily", "location": "Pacific Heights", "start": "11:15", "end": "19:45", "duration": 15},
        {"name": "Karen", "location": "Haight-Ashbury", "start": "11:45", "end": "17:30", "duration": 30},
        {"name": "Stephanie", "location": "Mission District", "start": "13:00", "end": "15:45", "duration": 75},
        {"name": "James", "location": "Chinatown", "start": "14:30", "end": "19:00", "duration": 120},
        {"name": "Steven", "location": "Russian Hill", "start": "14:00", "end": "20:00", "duration": 30},
        {"name": "Elizabeth", "location": "Alamo Square", "start": "13:00", "end": "17:15", "duration": 120},
        {"name": "William", "location": "Bayview", "start": "18:15", "end": "20:15", "duration": 90}
    ]
    
    # Convert time strings to minutes since 9:00
    def time_to_minutes(time_str):
        if ':' in time_str:
            parts = time_str.split(':')
            hours = int(parts[0])
            minutes = int(parts[1])
            return (hours - 9) * 60 + minutes
        return 0
    
    # Convert minutes since 9:00 back to time string
    def minutes_to_time(minutes):
        total_hours = 9 + minutes // 60
        total_minutes = minutes % 60
        return f"{total_hours}:{total_minutes:02d}"
    
    # Create problem
    problem = constraint.Problem()
    
    # Add variables for each friend: start time in minutes since 9:00
    for i, friend in enumerate(friends):
        friend_start = time_to_minutes(friend["start"])
        friend_end = time_to_minutes(friend["end"])
        friend_duration = friend["duration"]
        
        # Meeting must start after friend's availability starts and end before it ends
        max_start = friend_end - friend_duration
        problem.addVariable(f"start_{i}", range(friend_start, max_start + 1))
    
    # Add constraints for travel time between consecutive meetings
    for i in range(len(friends)):
        for j in range(len(friends)):
            if i != j:
                def travel_constraint(start_i, start_j, i=i, j=j):
                    # If meeting j is after meeting i
                    if start_j >= start_i + friends[i]["duration"]:
                        travel_time = travel_times.get(
                            (friends[i]["location"], friends[j]["location"]), 60
                        )
                        return start_j >= start_i + friends[i]["duration"] + travel_time
                    # If meeting i is after meeting j  
                    elif start_i >= start_j + friends[j]["duration"]:
                        travel_time = travel_times.get(
                            (friends[j]["location"], friends[i]["location"]), 60
                        )
                        return start_i >= start_j + friends[j]["duration"] + travel_time
                    # Meetings overlap or are too close
                    return False
                
                problem.addConstraint(travel_constraint, [f"start_{i}", f"start_{j}"])
    
    # Find solutions
    solutions = problem.getSolutions()
    
    if not solutions:
        # Fallback: try to schedule as many as possible
        best_solution = None
        best_count = 0
        
        # Try different orderings
        from itertools import permutations
        import random
        
        for attempt in range(100):
            order = list(range(len(friends)))
            random.shuffle(order)
            
            current_time = 0  # Start at 9:00
            scheduled = []
            current_location = "Richmond District"
            
            for idx in order:
                friend = friends[idx]
                friend_start = time_to_minutes(friend["start"])
                friend_end = time_to_minutes(friend["end"])
                friend_duration = friend["duration"]
                
                # Calculate travel time
                travel_time = travel_times.get((current_location, friend["location"]), 60)
                
                # Earliest possible start at this location
                earliest_start = max(current_time + travel_time, friend_start)
                
                # Check if we can schedule this meeting
                if earliest_start + friend_duration <= friend_end:
                    scheduled.append({
                        "friend": idx,
                        "start": earliest_start,
                        "end": earliest_start + friend_duration
                    })
                    current_time = earliest_start + friend_duration
                    current_location = friend["location"]
            
            if len(scheduled) > best_count:
                best_count = len(scheduled)
                best_solution = scheduled
        
        if best_solution:
            # Create itinerary from best solution
            itinerary = []
            for meeting in best_solution:
                friend_idx = meeting["friend"]
                friend = friends[friend_idx]
                itinerary.append({
                    "action": "meet",
                    "location": friend["location"],
                    "person": friend["name"],
                    "start_time": minutes_to_time(meeting["start"]),
                    "end_time": minutes_to_time(meeting["end"])
                })
            
            result = {"itinerary": itinerary}
            print(json.dumps(result, indent=2))
            return
    
    # If we found solutions with constraint solver, use the first one
    if solutions:
        solution = solutions[0]
        itinerary = []
        
        # Sort meetings by start time
        meetings = []
        for i in range(len(friends)):
            if f"start_{i}" in solution:
                meetings.append({
                    "friend": i,
                    "start": solution[f"start_{i}"],
                    "end": solution[f"start_{i}"] + friends[i]["duration"]
                })
        
        meetings.sort(key=lambda x: x["start"])
        
        for meeting in meetings:
            friend_idx = meeting["friend"]
            friend = friends[friend_idx]
            itinerary.append({
                "action": "meet",
                "location": friend["location"],
                "person": friend["name"],
                "start_time": minutes_to_time(meeting["start"]),
                "end_time": minutes_to_time(meeting["end"])
            })
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        # No solution found
        print(json.dumps({"itinerary": []}, indent=2))

if __name__ == "__main__":
    main()