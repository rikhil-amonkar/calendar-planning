import constraint
from datetime import datetime, timedelta
import json

def main():
    # Define all locations
    locations = [
        "Pacific Heights", "Marina District", "The Castro", "Richmond District", 
        "Alamo Square", "Financial District", "Presidio", "Mission District", 
        "Nob Hill", "Russian Hill"
    ]
    
    # Travel times matrix (in minutes)
    travel_times = {
        ("Pacific Heights", "Marina District"): 6,
        ("Pacific Heights", "The Castro"): 16,
        ("Pacific Heights", "Richmond District"): 12,
        ("Pacific Heights", "Alamo Square"): 10,
        ("Pacific Heights", "Financial District"): 13,
        ("Pacific Heights", "Presidio"): 11,
        ("Pacific Heights", "Mission District"): 15,
        ("Pacific Heights", "Nob Hill"): 8,
        ("Pacific Heights", "Russian Hill"): 7,
        ("Marina District", "Pacific Heights"): 7,
        ("Marina District", "The Castro"): 22,
        ("Marina District", "Richmond District"): 11,
        ("Marina District", "Alamo Square"): 15,
        ("Marina District", "Financial District"): 17,
        ("Marina District", "Presidio"): 10,
        ("Marina District", "Mission District"): 20,
        ("Marina District", "Nob Hill"): 12,
        ("Marina District", "Russian Hill"): 8,
        ("The Castro", "Pacific Heights"): 16,
        ("The Castro", "Marina District"): 21,
        ("The Castro", "Richmond District"): 16,
        ("The Castro", "Alamo Square"): 8,
        ("The Castro", "Financial District"): 21,
        ("The Castro", "Presidio"): 20,
        ("The Castro", "Mission District"): 7,
        ("The Castro", "Nob Hill"): 16,
        ("The Castro", "Russian Hill"): 18,
        ("Richmond District", "Pacific Heights"): 10,
        ("Richmond District", "Marina District"): 9,
        ("Richmond District", "The Castro"): 16,
        ("Richmond District", "Alamo Square"): 13,
        ("Richmond District", "Financial District"): 22,
        ("Richmond District", "Presidio"): 7,
        ("Richmond District", "Mission District"): 20,
        ("Richmond District", "Nob Hill"): 17,
        ("Richmond District", "Russian Hill"): 13,
        ("Alamo Square", "Pacific Heights"): 10,
        ("Alamo Square", "Marina District"): 15,
        ("Alamo Square", "The Castro"): 8,
        ("Alamo Square", "Richmond District"): 11,
        ("Alamo Square", "Financial District"): 17,
        ("Alamo Square", "Presidio"): 17,
        ("Alamo Square", "Mission District"): 10,
        ("Alamo Square", "Nob Hill"): 11,
        ("Alamo Square", "Russian Hill"): 13,
        ("Financial District", "Pacific Heights"): 13,
        ("Financial District", "Marina District"): 15,
        ("Financial District", "The Castro"): 20,
        ("Financial District", "Richmond District"): 21,
        ("Financial District", "Alamo Square"): 17,
        ("Financial District", "Presidio"): 22,
        ("Financial District", "Mission District"): 17,
        ("Financial District", "Nob Hill"): 8,
        ("Financial District", "Russian Hill"): 11,
        ("Presidio", "Pacific Heights"): 11,
        ("Presidio", "Marina District"): 11,
        ("Presidio", "The Castro"): 21,
        ("Presidio", "Richmond District"): 7,
        ("Presidio", "Alamo Square"): 19,
        ("Presidio", "Financial District"): 23,
        ("Presidio", "Mission District"): 26,
        ("Presidio", "Nob Hill"): 18,
        ("Presidio", "Russian Hill"): 14,
        ("Mission District", "Pacific Heights"): 16,
        ("Mission District", "Marina District"): 19,
        ("Mission District", "The Castro"): 7,
        ("Mission District", "Richmond District"): 20,
        ("Mission District", "Alamo Square"): 11,
        ("Mission District", "Financial District"): 15,
        ("Mission District", "Presidio"): 25,
        ("Mission District", "Nob Hill"): 12,
        ("Mission District", "Russian Hill"): 15,
        ("Nob Hill", "Pacific Heights"): 8,
        ("Nob Hill", "Marina District"): 11,
        ("Nob Hill", "The Castro"): 17,
        ("Nob Hill", "Richmond District"): 14,
        ("Nob Hill", "Alamo Square"): 11,
        ("Nob Hill", "Financial District"): 9,
        ("Nob Hill", "Presidio"): 17,
        ("Nob Hill", "Mission District"): 13,
        ("Nob Hill", "Russian Hill"): 5,
        ("Russian Hill", "Pacific Heights"): 7,
        ("Russian Hill", "Marina District"): 7,
        ("Russian Hill", "The Castro"): 21,
        ("Russian Hill", "Richmond District"): 14,
        ("Russian Hill", "Alamo Square"): 15,
        ("Russian Hill", "Financial District"): 11,
        ("Russian Hill", "Presidio"): 14,
        ("Russian Hill", "Mission District"): 16,
        ("Russian Hill", "Nob Hill"): 5,
    }
    
    # Friend constraints
    friends = [
        {"name": "Linda", "location": "Marina District", "start": "18:00", "end": "22:00", "duration": 30},
        {"name": "Kenneth", "location": "The Castro", "start": "14:45", "end": "16:15", "duration": 30},
        {"name": "Kimberly", "location": "Richmond District", "start": "14:15", "end": "22:00", "duration": 30},
        {"name": "Paul", "location": "Alamo Square", "start": "21:00", "end": "21:30", "duration": 15},
        {"name": "Carol", "location": "Financial District", "start": "10:15", "end": "12:00", "duration": 60},
        {"name": "Brian", "location": "Presidio", "start": "10:00", "end": "21:30", "duration": 75},
        {"name": "Laura", "location": "Mission District", "start": "16:15", "end": "20:30", "duration": 30},
        {"name": "Sandra", "location": "Nob Hill", "start": "9:15", "end": "18:30", "duration": 60},
        {"name": "Karen", "location": "Russian Hill", "start": "18:30", "end": "22:00", "duration": 75}
    ]
    
    # Convert time strings to minutes since 9:00
    def time_to_minutes(time_str):
        time_obj = datetime.strptime(time_str, "%H:%M")
        base_time = datetime.strptime("9:00", "%H:%M")
        delta = time_obj - base_time
        return int(delta.total_seconds() / 60)
    
    # Convert minutes since 9:00 to time string
    def minutes_to_time(minutes):
        base_time = datetime.strptime("9:00", "%H:%M")
        result_time = base_time + timedelta(minutes=minutes)
        return result_time.strftime("%H:%M").lstrip("0")
    
    # Create problem
    problem = constraint.Problem()
    
    # Add variables for each friend (start time in minutes since 9:00)
    for i, friend in enumerate(friends):
        friend_start = time_to_minutes(friend["start"])
        friend_end = time_to_minutes(friend["end"])
        # Meeting must start at least at friend's start time and end by friend's end time
        problem.addVariable(f"start_{i}", range(friend_start, friend_end - friend["duration"] + 1))
    
    # Add constraints for travel time between consecutive meetings
    for i in range(len(friends)):
        for j in range(i + 1, len(friends)):
            def travel_constraint(start_i, start_j, i=i, j=j):
                # Calculate end time of first meeting
                end_i = start_i + friends[i]["duration"]
                
                # Calculate travel time between locations
                loc_i = friends[i]["location"]
                loc_j = friends[j]["location"]
                travel_time = travel_times.get((loc_i, loc_j), 30)  # Default to 30 if not found
                
                # Check if there's enough time to travel between meetings
                if start_j >= end_i + travel_time:
                    return True
                return False
            
            problem.addConstraint(travel_constraint, [f"start_{i}", f"start_{j}"])
    
    # Try to find a solution
    solutions = problem.getSolutions()
    
    if not solutions:
        # If no solution found, try a simpler approach - meet friends in order of availability
        itinerary = []
        current_time = time_to_minutes("9:00")  # Start at 9:00
        current_location = "Pacific Heights"
        
        # Sort friends by their availability start time
        sorted_friends = sorted(friends, key=lambda x: time_to_minutes(x["start"]))
        
        for friend in sorted_friends:
            # Calculate travel time to friend's location
            travel_time = travel_times.get((current_location, friend["location"]), 30)
            
            # Calculate earliest possible start time
            earliest_start = max(current_time + travel_time, time_to_minutes(friend["start"]))
            
            # Check if we can meet within friend's availability
            if earliest_start + friend["duration"] <= time_to_minutes(friend["end"]):
                # Add meeting to itinerary
                itinerary.append({
                    "action": "meet",
                    "location": friend["location"],
                    "person": friend["name"],
                    "start_time": minutes_to_time(earliest_start),
                    "end_time": minutes_to_time(earliest_start + friend["duration"])
                })
                
                # Update current time and location
                current_time = earliest_start + friend["duration"]
                current_location = friend["location"]
        
        result = {"itinerary": itinerary}
    else:
        # Use the first solution found
        solution = solutions[0]
        itinerary = []
        
        # Create list of meetings with their start times
        meetings = []
        for i, friend in enumerate(friends):
            meetings.append({
                "friend": friend,
                "start_time": solution[f"start_{i}"],
                "index": i
            })
        
        # Sort meetings by start time
        meetings.sort(key=lambda x: x["start_time"])
        
        # Build itinerary
        for meeting in meetings:
            friend = meeting["friend"]
            itinerary.append({
                "action": "meet",
                "location": friend["location"],
                "person": friend["name"],
                "start_time": minutes_to_time(meeting["start_time"]),
                "end_time": minutes_to_time(meeting["start_time"] + friend["duration"])
            })
        
        result = {"itinerary": itinerary}
    
    # Output as JSON
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()