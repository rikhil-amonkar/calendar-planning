import constraint
from datetime import datetime, timedelta
import json

def main():
    # Define locations
    locations = [
        "Pacific Heights", "Golden Gate Park", "The Castro", "Bayview", 
        "Marina District", "Union Square", "Sunset District", "Alamo Square", 
        "Financial District", "Mission District"
    ]
    
    # Travel times matrix (minutes)
    travel_times = {
        ("Pacific Heights", "Golden Gate Park"): 15,
        ("Pacific Heights", "The Castro"): 16,
        ("Pacific Heights", "Bayview"): 22,
        ("Pacific Heights", "Marina District"): 6,
        ("Pacific Heights", "Union Square"): 12,
        ("Pacific Heights", "Sunset District"): 21,
        ("Pacific Heights", "Alamo Square"): 10,
        ("Pacific Heights", "Financial District"): 13,
        ("Pacific Heights", "Mission District"): 15,
        ("Golden Gate Park", "Pacific Heights"): 16,
        ("Golden Gate Park", "The Castro"): 13,
        ("Golden Gate Park", "Bayview"): 23,
        ("Golden Gate Park", "Marina District"): 16,
        ("Golden Gate Park", "Union Square"): 22,
        ("Golden Gate Park", "Sunset District"): 10,
        ("Golden Gate Park", "Alamo Square"): 9,
        ("Golden Gate Park", "Financial District"): 26,
        ("Golden Gate Park", "Mission District"): 17,
        ("The Castro", "Pacific Heights"): 16,
        ("The Castro", "Golden Gate Park"): 11,
        ("The Castro", "Bayview"): 19,
        ("The Castro", "Marina District"): 21,
        ("The Castro", "Union Square"): 19,
        ("The Castro", "Sunset District"): 17,
        ("The Castro", "Alamo Square"): 8,
        ("The Castro", "Financial District"): 21,
        ("The Castro", "Mission District"): 7,
        ("Bayview", "Pacific Heights"): 23,
        ("Bayview", "Golden Gate Park"): 22,
        ("Bayview", "The Castro"): 19,
        ("Bayview", "Marina District"): 27,
        ("Bayview", "Union Square"): 18,
        ("Bayview", "Sunset District"): 23,
        ("Bayview", "Alamo Square"): 16,
        ("Bayview", "Financial District"): 19,
        ("Bayview", "Mission District"): 13,
        ("Marina District", "Pacific Heights"): 7,
        ("Marina District", "Golden Gate Park"): 18,
        ("Marina District", "The Castro"): 22,
        ("Marina District", "Bayview"): 27,
        ("Marina District", "Union Square"): 16,
        ("Marina District", "Sunset District"): 19,
        ("Marina District", "Alamo Square"): 15,
        ("Marina District", "Financial District"): 17,
        ("Marina District", "Mission District"): 20,
        ("Union Square", "Pacific Heights"): 15,
        ("Union Square", "Golden Gate Park"): 22,
        ("Union Square", "The Castro"): 17,
        ("Union Square", "Bayview"): 15,
        ("Union Square", "Marina District"): 18,
        ("Union Square", "Sunset District"): 27,
        ("Union Square", "Alamo Square"): 15,
        ("Union Square", "Financial District"): 9,
        ("Union Square", "Mission District"): 14,
        ("Sunset District", "Pacific Heights"): 21,
        ("Sunset District", "Golden Gate Park"): 11,
        ("Sunset District", "The Castro"): 17,
        ("Sunset District", "Bayview"): 22,
        ("Sunset District", "Marina District"): 21,
        ("Sunset District", "Union Square"): 30,
        ("Sunset District", "Alamo Square"): 17,
        ("Sunset District", "Financial District"): 30,
        ("Sunset District", "Mission District"): 25,
        ("Alamo Square", "Pacific Heights"): 10,
        ("Alamo Square", "Golden Gate Park"): 9,
        ("Alamo Square", "The Castro"): 8,
        ("Alamo Square", "Bayview"): 16,
        ("Alamo Square", "Marina District"): 15,
        ("Alamo Square", "Union Square"): 14,
        ("Alamo Square", "Sunset District"): 16,
        ("Alamo Square", "Financial District"): 17,
        ("Alamo Square", "Mission District"): 10,
        ("Financial District", "Pacific Heights"): 13,
        ("Financial District", "Golden Gate Park"): 23,
        ("Financial District", "The Castro"): 20,
        ("Financial District", "Bayview"): 19,
        ("Financial District", "Marina District"): 15,
        ("Financial District", "Union Square"): 9,
        ("Financial District", "Sunset District"): 30,
        ("Financial District", "Alamo Square"): 17,
        ("Financial District", "Mission District"): 17,
        ("Mission District", "Pacific Heights"): 16,
        ("Mission District", "Golden Gate Park"): 17,
        ("Mission District", "The Castro"): 7,
        ("Mission District", "Bayview"): 14,
        ("Mission District", "Marina District"): 19,
        ("Mission District", "Union Square"): 15,
        ("Mission District", "Sunset District"): 24,
        ("Mission District", "Alamo Square"): 11,
        ("Mission District", "Financial District"): 15
    }
    
    # Friend constraints
    friends = [
        {"name": "Helen", "location": "Golden Gate Park", "start": "9:30", "end": "12:15", "min_duration": 45},
        {"name": "Steven", "location": "The Castro", "start": "20:15", "end": "22:00", "min_duration": 105},
        {"name": "Deborah", "location": "Bayview", "start": "8:30", "end": "12:00", "min_duration": 30},
        {"name": "Matthew", "location": "Marina District", "start": "9:15", "end": "14:15", "min_duration": 45},
        {"name": "Joseph", "location": "Union Square", "start": "14:15", "end": "18:45", "min_duration": 120},
        {"name": "Ronald", "location": "Sunset District", "start": "16:00", "end": "20:45", "min_duration": 60},
        {"name": "Robert", "location": "Alamo Square", "start": "18:30", "end": "21:15", "min_duration": 120},
        {"name": "Rebecca", "location": "Financial District", "start": "14:45", "end": "16:15", "min_duration": 30},
        {"name": "Elizabeth", "location": "Mission District", "start": "18:30", "end": "21:00", "min_duration": 120}
    ]
    
    # Convert time strings to minutes since 9:00
    def time_to_minutes(time_str):
        if ':' in time_str:
            hours, minutes = map(int, time_str.split(':'))
            return (hours - 9) * 60 + minutes
        return 0
    
    # Convert minutes to time string
    def minutes_to_time(minutes):
        total_hours = 9 + minutes // 60
        total_minutes = minutes % 60
        return f"{total_hours}:{total_minutes:02d}"
    
    # Create problem
    problem = constraint.Problem()
    
    # Add variables for each friend: start time and duration
    for i, friend in enumerate(friends):
        friend_start_min = time_to_minutes(friend["start"])
        friend_end_min = time_to_minutes(friend["end"])
        
        # Start time variable (in minutes from 9:00)
        problem.addVariable(f"start_{i}", range(friend_start_min, friend_end_min - friend["min_duration"] + 1))
        
        # Duration variable (at least min_duration, up to available time)
        problem.addVariable(f"duration_{i}", range(friend["min_duration"], friend_end_min - friend_start_min + 1))
    
    # Add travel time constraints
    def travel_constraint(*args):
        # args: start_0, duration_0, start_1, duration_1, ...
        n = len(friends)
        
        # Create list of meetings with start, end, and location
        meetings = []
        for i in range(n):
            start = args[i * 2]
            duration = args[i * 2 + 1]
            end = start + duration
            meetings.append({
                "start": start,
                "end": end,
                "location": friends[i]["location"]
            })
        
        # Sort meetings by start time
        meetings.sort(key=lambda x: x["start"])
        
        # Check travel times between consecutive meetings
        for i in range(len(meetings) - 1):
            current = meetings[i]
            next_meeting = meetings[i + 1]
            
            # Calculate travel time between locations
            travel_time = travel_times.get((current["location"], next_meeting["location"]), 60)
            
            # Check if there's enough time to travel
            if current["end"] + travel_time > next_meeting["start"]:
                return False
        
        return True
    
    # Add all variables to the constraint
    all_vars = []
    for i in range(len(friends)):
        all_vars.extend([f"start_{i}", f"duration_{i}"])
    
    problem.addConstraint(travel_constraint, all_vars)
    
    # Add constraint that meetings don't overlap (handled by travel constraint)
    
    # Objective: maximize total meeting time
    def objective(*args):
        total_duration = 0
        for i in range(len(friends)):
            total_duration += args[i * 2 + 1]  # duration_i
        return total_duration
    
    # Find solution
    solutions = problem.getSolutions()
    
    if not solutions:
        # Fallback: try to meet as many friends as possible with minimal durations
        best_solution = None
        best_score = -1
        
        for friend_count in range(len(friends), 0, -1):
            # Reset problem
            problem = constraint.Problem()
            
            # Add variables with minimal durations only
            for i, friend in enumerate(friends):
                friend_start_min = time_to_minutes(friend["start"])
                friend_end_min = time_to_minutes(friend["end"])
                
                problem.addVariable(f"start_{i}", range(friend_start_min, friend_end_min - friend["min_duration"] + 1))
                problem.addVariable(f"duration_{i}", [friend["min_duration"]])
            
            problem.addConstraint(travel_constraint, all_vars)
            solutions = problem.getSolutions()
            
            if solutions:
                best_solution = solutions[0]
                best_score = friend_count
                break
        
        if best_solution is None:
            # Last resort: meet just one friend
            best_solution = {}
            for i in range(len(friends)):
                friend = friends[i]
                friend_start_min = time_to_minutes(friend["start"])
                friend_end_min = time_to_minutes(friend["end"])
                best_solution[f"start_{i}"] = friend_start_min
                best_solution[f"duration_{i}"] = friend["min_duration"]
    else:
        # Find solution with maximum total duration
        best_solution = max(solutions, key=lambda sol: sum(sol[f"duration_{i}"] for i in range(len(friends))))
    
    # Build itinerary
    itinerary = []
    
    # Create list of meetings
    meetings = []
    for i in range(len(friends)):
        if f"start_{i}" in best_solution:
            start_min = best_solution[f"start_{i}"]
            duration = best_solution[f"duration_{i}"]
            end_min = start_min + duration
            
            meetings.append({
                "person": friends[i]["name"],
                "location": friends[i]["location"],
                "start": minutes_to_time(start_min),
                "end": minutes_to_time(end_min)
            })
    
    # Sort by start time
    meetings.sort(key=lambda x: time_to_minutes(x["start"]))
    
    # Add travel actions
    current_location = "Pacific Heights"
    current_time = time_to_minutes("9:00")
    
    for meeting in meetings:
        meeting_start = time_to_minutes(meeting["start"])
        
        # Add travel if needed
        if current_location != meeting["location"]:
            travel_time = travel_times.get((current_location, meeting["location"]), 30)
            
            # Check if we have enough time to travel
            if current_time + travel_time <= meeting_start:
                travel_start = minutes_to_time(current_time)
                travel_end = minutes_to_time(current_time + travel_time)
                
                itinerary.append({
                    "action": "travel",
                    "from": current_location,
                    "to": meeting["location"],
                    "start_time": travel_start,
                    "end_time": travel_end
                })
            
            current_time = meeting_start
        
        # Add meeting
        itinerary.append({
            "action": "meet",
            "location": meeting["location"],
            "person": meeting["person"],
            "start_time": meeting["start"],
            "end_time": meeting["end"]
        })
        
        current_location = meeting["location"]
        current_time = time_to_minutes(meeting["end"])
    
    # Output as JSON
    result = {
        "itinerary": itinerary
    }
    
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()