import constraint
from datetime import datetime, timedelta
import json

def main():
    # Define all locations
    locations = [
        "Sunset District", "Presidio", "Nob Hill", "Pacific Heights", "Mission District",
        "Marina District", "North Beach", "Russian Hill", "Richmond District", 
        "Embarcadero", "Alamo Square"
    ]
    
    # Travel times dictionary (in minutes)
    travel_times = {
        ("Sunset District", "Presidio"): 16,
        ("Sunset District", "Nob Hill"): 27,
        ("Sunset District", "Pacific Heights"): 21,
        ("Sunset District", "Mission District"): 25,
        ("Sunset District", "Marina District"): 21,
        ("Sunset District", "North Beach"): 28,
        ("Sunset District", "Russian Hill"): 24,
        ("Sunset District", "Richmond District"): 12,
        ("Sunset District", "Embarcadero"): 30,
        ("Sunset District", "Alamo Square"): 17,
        ("Presidio", "Sunset District"): 15,
        ("Presidio", "Nob Hill"): 18,
        ("Presidio", "Pacific Heights"): 11,
        ("Presidio", "Mission District"): 26,
        ("Presidio", "Marina District"): 11,
        ("Presidio", "North Beach"): 18,
        ("Presidio", "Russian Hill"): 14,
        ("Presidio", "Richmond District"): 7,
        ("Presidio", "Embarcadero"): 20,
        ("Presidio", "Alamo Square"): 19,
        ("Nob Hill", "Sunset District"): 24,
        ("Nob Hill", "Presidio"): 17,
        ("Nob Hill", "Pacific Heights"): 8,
        ("Nob Hill", "Mission District"): 13,
        ("Nob Hill", "Marina District"): 11,
        ("Nob Hill", "North Beach"): 8,
        ("Nob Hill", "Russian Hill"): 5,
        ("Nob Hill", "Richmond District"): 14,
        ("Nob Hill", "Embarcadero"): 9,
        ("Nob Hill", "Alamo Square"): 11,
        ("Pacific Heights", "Sunset District"): 21,
        ("Pacific Heights", "Presidio"): 11,
        ("Pacific Heights", "Nob Hill"): 8,
        ("Pacific Heights", "Mission District"): 15,
        ("Pacific Heights", "Marina District"): 6,
        ("Pacific Heights", "North Beach"): 9,
        ("Pacific Heights", "Russian Hill"): 7,
        ("Pacific Heights", "Richmond District"): 12,
        ("Pacific Heights", "Embarcadero"): 10,
        ("Pacific Heights", "Alamo Square"): 10,
        ("Mission District", "Sunset District"): 24,
        ("Mission District", "Presidio"): 25,
        ("Mission District", "Nob Hill"): 12,
        ("Mission District", "Pacific Heights"): 16,
        ("Mission District", "Marina District"): 19,
        ("Mission District", "North Beach"): 17,
        ("Mission District", "Russian Hill"): 15,
        ("Mission District", "Richmond District"): 20,
        ("Mission District", "Embarcadero"): 19,
        ("Mission District", "Alamo Square"): 11,
        ("Marina District", "Sunset District"): 19,
        ("Marina District", "Presidio"): 10,
        ("Marina District", "Nob Hill"): 12,
        ("Marina District", "Pacific Heights"): 7,
        ("Marina District", "Mission District"): 20,
        ("Marina District", "North Beach"): 11,
        ("Marina District", "Russian Hill"): 8,
        ("Marina District", "Richmond District"): 11,
        ("Marina District", "Embarcadero"): 14,
        ("Marina District", "Alamo Square"): 15,
        ("North Beach", "Sunset District"): 27,
        ("North Beach", "Presidio"): 17,
        ("North Beach", "Nob Hill"): 7,
        ("North Beach", "Pacific Heights"): 8,
        ("North Beach", "Mission District"): 18,
        ("North Beach", "Marina District"): 9,
        ("North Beach", "Russian Hill"): 4,
        ("North Beach", "Richmond District"): 18,
        ("North Beach", "Embarcadero"): 6,
        ("North Beach", "Alamo Square"): 16,
        ("Russian Hill", "Sunset District"): 23,
        ("Russian Hill", "Presidio"): 14,
        ("Russian Hill", "Nob Hill"): 5,
        ("Russian Hill", "Pacific Heights"): 7,
        ("Russian Hill", "Mission District"): 16,
        ("Russian Hill", "Marina District"): 7,
        ("Russian Hill", "North Beach"): 5,
        ("Russian Hill", "Richmond District"): 14,
        ("Russian Hill", "Embarcadero"): 8,
        ("Russian Hill", "Alamo Square"): 15,
        ("Richmond District", "Sunset District"): 11,
        ("Richmond District", "Presidio"): 7,
        ("Richmond District", "Nob Hill"): 17,
        ("Richmond District", "Pacific Heights"): 10,
        ("Richmond District", "Mission District"): 20,
        ("Richmond District", "Marina District"): 9,
        ("Richmond District", "North Beach"): 17,
        ("Richmond District", "Russian Hill"): 13,
        ("Richmond District", "Embarcadero"): 19,
        ("Richmond District", "Alamo Square"): 13,
        ("Embarcadero", "Sunset District"): 30,
        ("Embarcadero", "Presidio"): 20,
        ("Embarcadero", "Nob Hill"): 10,
        ("Embarcadero", "Pacific Heights"): 11,
        ("Embarcadero", "Mission District"): 20,
        ("Embarcadero", "Marina District"): 12,
        ("Embarcadero", "North Beach"): 5,
        ("Embarcadero", "Russian Hill"): 8,
        ("Embarcadero", "Richmond District"): 21,
        ("Embarcadero", "Alamo Square"): 19,
        ("Alamo Square", "Sunset District"): 16,
        ("Alamo Square", "Presidio"): 17,
        ("Alamo Square", "Nob Hill"): 11,
        ("Alamo Square", "Pacific Heights"): 10,
        ("Alamo Square", "Mission District"): 10,
        ("Alamo Square", "Marina District"): 15,
        ("Alamo Square", "North Beach"): 15,
        ("Alamo Square", "Russian Hill"): 13,
        ("Alamo Square", "Richmond District"): 11,
        ("Alamo Square", "Embarcadero"): 16
    }
    
    # Friend constraints
    friends = [
        {"name": "Charles", "location": "Presidio", "available_start": "13:15", "available_end": "15:00", "min_duration": 105},
        {"name": "Robert", "location": "Nob Hill", "available_start": "13:15", "available_end": "17:30", "min_duration": 90},
        {"name": "Nancy", "location": "Pacific Heights", "available_start": "14:45", "available_end": "22:00", "min_duration": 105},
        {"name": "Brian", "location": "Mission District", "available_start": "15:30", "available_end": "22:00", "min_duration": 60},
        {"name": "Kimberly", "location": "Marina District", "available_start": "17:00", "available_end": "19:45", "min_duration": 75},
        {"name": "David", "location": "North Beach", "available_start": "14:45", "available_end": "16:30", "min_duration": 75},
        {"name": "William", "location": "Russian Hill", "available_start": "12:30", "available_end": "19:15", "min_duration": 120},
        {"name": "Jeffrey", "location": "Richmond District", "available_start": "12:00", "available_end": "19:15", "min_duration": 45},
        {"name": "Karen", "location": "Embarcadero", "available_start": "14:15", "available_end": "20:45", "min_duration": 60},
        {"name": "Joshua", "location": "Alamo Square", "available_start": "18:45", "available_end": "22:00", "min_duration": 60}
    ]
    
    # Convert time strings to minutes since 9:00
    def time_to_minutes(time_str):
        if ':' in time_str:
            hours, minutes = map(int, time_str.split(':'))
        else:
            hours = int(time_str)
            minutes = 0
        return (hours - 9) * 60 + minutes
    
    # Convert minutes since 9:00 to time string
    def minutes_to_time(minutes):
        total_hours = 9 + minutes // 60
        total_minutes = minutes % 60
        return f"{total_hours}:{total_minutes:02d}"
    
    # Create problem
    problem = constraint.Problem()
    
    # Add variables for each friend: start time and duration
    for i, friend in enumerate(friends):
        available_start = time_to_minutes(friend["available_start"])
        available_end = time_to_minutes(friend["available_end"])
        min_duration = friend["min_duration"]
        
        # Start time must be within availability window
        problem.addVariable(f"start_{i}", range(available_start, available_end - min_duration + 1))
        # Duration must be at least minimum required
        problem.addVariable(f"duration_{i}", range(min_duration, available_end - available_start + 1))
    
    # Add constraints to ensure no overlaps considering travel time
    def no_overlap_constraint(*args):
        n = len(friends)
        starts = args[:n]
        durations = args[n:]
        
        # Create meeting intervals
        meetings = []
        for i in range(n):
            end_time = starts[i] + durations[i]
            meetings.append((starts[i], end_time, friends[i]["location"]))
        
        # Sort by start time
        meetings.sort()
        
        # Check for overlaps considering travel time
        for i in range(len(meetings) - 1):
            current_end = meetings[i][1]
            next_start = meetings[i + 1][0]
            current_loc = meetings[i][2]
            next_loc = meetings[i + 1][2]
            
            travel_time = travel_times.get((current_loc, next_loc), 30)  # Default to 30 if not found
            
            if current_end + travel_time > next_start:
                return False
        
        return True
    
    # Get all variable names for the constraint
    all_vars = []
    for i in range(len(friends)):
        all_vars.append(f"start_{i}")
        all_vars.append(f"duration_{i}")
    
    problem.addConstraint(no_overlap_constraint, all_vars)
    
    # Add constraint to maximize total meeting time
    def maximize_time(*args):
        n = len(friends)
        durations = args[n:]
        return sum(durations)
    
    # Find solution that maximizes total meeting time
    solutions = problem.getSolutions()
    
    if not solutions:
        # Fallback: try to meet as many friends as possible with minimum durations
        best_solution = None
        best_score = -1
        
        for solution in problem.getSolutions():
            n = len(friends)
            durations = [solution[f"duration_{i}"] for i in range(n)]
            score = sum(durations)
            
            if score > best_score:
                best_score = score
                best_solution = solution
        
        solution = best_solution
    else:
        # Find solution with maximum total meeting time
        best_solution = None
        best_score = -1
        
        for sol in solutions:
            n = len(friends)
            durations = [sol[f"duration_{i}"] for i in range(n)]
            score = sum(durations)
            
            if score > best_score:
                best_score = score
                best_solution = sol
        
        solution = best_solution
    
    # Build itinerary
    itinerary = []
    current_time = 0  # Start at 9:00 (0 minutes)
    current_location = "Sunset District"
    
    # Create list of meetings from solution
    meetings = []
    for i, friend in enumerate(friends):
        if solution:
            start_time = solution[f"start_{i}"]
            duration = solution[f"duration_{i}"]
            end_time = start_time + duration
            
            meetings.append({
                "friend": friend,
                "start": start_time,
                "end": end_time,
                "location": friend["location"]
            })
    
    # Sort meetings by start time
    meetings.sort(key=lambda x: x["start"])
    
    # Add travel to first meeting
    first_meeting = meetings[0]
    travel_time = travel_times.get((current_location, first_meeting["location"]), 30)
    
    if travel_time > 0:
        itinerary.append({
            "action": "travel",
            "location": first_meeting["location"],
            "person": "",
            "start_time": minutes_to_time(current_time),
            "end_time": minutes_to_time(current_time + travel_time)
        })
    
    current_time += travel_time
    current_location = first_meeting["location"]
    
    # Add meetings and travel between them
    for i, meeting in enumerate(meetings):
        # Add meeting
        itinerary.append({
            "action": "meet",
            "location": meeting["location"],
            "person": meeting["friend"]["name"],
            "start_time": minutes_to_time(meeting["start"]),
            "end_time": minutes_to_time(meeting["end"])
        })
        
        current_time = meeting["end"]
        current_location = meeting["location"]
        
        # Add travel to next meeting if there is one
        if i < len(meetings) - 1:
            next_meeting = meetings[i + 1]
            travel_time = travel_times.get((current_location, next_meeting["location"]), 30)
            
            if current_time + travel_time <= next_meeting["start"]:
                itinerary.append({
                    "action": "travel",
                    "location": next_meeting["location"],
                    "person": "",
                    "start_time": minutes_to_time(current_time),
                    "end_time": minutes_to_time(current_time + travel_time)
                })
                current_time += travel_time
                current_location = next_meeting["location"]
    
    # Output result
    result = {
        "itinerary": itinerary
    }
    
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()