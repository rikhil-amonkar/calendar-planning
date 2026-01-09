import constraint
from datetime import datetime, timedelta
import json

def main():
    # Define locations and travel times
    locations = [
        "Union Square", "The Castro", "North Beach", "Embarcadero", 
        "Alamo Square", "Nob Hill", "Presidio", "Fisherman's Wharf", 
        "Mission District", "Haight-Ashbury"
    ]
    
    # Travel times matrix (in minutes)
    travel_times = {
        ("Union Square", "The Castro"): 17,
        ("Union Square", "North Beach"): 10,
        ("Union Square", "Embarcadero"): 11,
        ("Union Square", "Alamo Square"): 15,
        ("Union Square", "Nob Hill"): 9,
        ("Union Square", "Presidio"): 24,
        ("Union Square", "Fisherman's Wharf"): 15,
        ("Union Square", "Mission District"): 14,
        ("Union Square", "Haight-Ashbury"): 18,
        ("The Castro", "Union Square"): 19,
        ("The Castro", "North Beach"): 20,
        ("The Castro", "Embarcadero"): 22,
        ("The Castro", "Alamo Square"): 8,
        ("The Castro", "Nob Hill"): 16,
        ("The Castro", "Presidio"): 20,
        ("The Castro", "Fisherman's Wharf"): 24,
        ("The Castro", "Mission District"): 7,
        ("The Castro", "Haight-Ashbury"): 6,
        ("North Beach", "Union Square"): 7,
        ("North Beach", "The Castro"): 23,
        ("North Beach", "Embarcadero"): 6,
        ("North Beach", "Alamo Square"): 16,
        ("North Beach", "Nob Hill"): 7,
        ("North Beach", "Presidio"): 17,
        ("North Beach", "Fisherman's Wharf"): 5,
        ("North Beach", "Mission District"): 18,
        ("North Beach", "Haight-Ashbury"): 18,
        ("Embarcadero", "Union Square"): 10,
        ("Embarcadero", "The Castro"): 25,
        ("Embarcadero", "North Beach"): 5,
        ("Embarcadero", "Alamo Square"): 19,
        ("Embarcadero", "Nob Hill"): 10,
        ("Embarcadero", "Presidio"): 20,
        ("Embarcadero", "Fisherman's Wharf"): 6,
        ("Embarcadero", "Mission District"): 20,
        ("Embarcadero", "Haight-Ashbury"): 21,
        ("Alamo Square", "Union Square"): 14,
        ("Alamo Square", "The Castro"): 8,
        ("Alamo Square", "North Beach"): 15,
        ("Alamo Square", "Embarcadero"): 16,
        ("Alamo Square", "Nob Hill"): 11,
        ("Alamo Square", "Presidio"): 17,
        ("Alamo Square", "Fisherman's Wharf"): 19,
        ("Alamo Square", "Mission District"): 10,
        ("Alamo Square", "Haight-Ashbury"): 5,
        ("Nob Hill", "Union Square"): 7,
        ("Nob Hill", "The Castro"): 17,
        ("Nob Hill", "North Beach"): 8,
        ("Nob Hill", "Embarcadero"): 9,
        ("Nob Hill", "Alamo Square"): 11,
        ("Nob Hill", "Presidio"): 17,
        ("Nob Hill", "Fisherman's Wharf"): 10,
        ("Nob Hill", "Mission District"): 13,
        ("Nob Hill", "Haight-Ashbury"): 13,
        ("Presidio", "Union Square"): 22,
        ("Presidio", "The Castro"): 21,
        ("Presidio", "North Beach"): 18,
        ("Presidio", "Embarcadero"): 20,
        ("Presidio", "Alamo Square"): 19,
        ("Presidio", "Nob Hill"): 18,
        ("Presidio", "Fisherman's Wharf"): 19,
        ("Presidio", "Mission District"): 26,
        ("Presidio", "Haight-Ashbury"): 15,
        ("Fisherman's Wharf", "Union Square"): 13,
        ("Fisherman's Wharf", "The Castro"): 27,
        ("Fisherman's Wharf", "North Beach"): 6,
        ("Fisherman's Wharf", "Embarcadero"): 8,
        ("Fisherman's Wharf", "Alamo Square"): 21,
        ("Fisherman's Wharf", "Nob Hill"): 11,
        ("Fisherman's Wharf", "Presidio"): 17,
        ("Fisherman's Wharf", "Mission District"): 22,
        ("Fisherman's Wharf", "Haight-Ashbury"): 22,
        ("Mission District", "Union Square"): 15,
        ("Mission District", "The Castro"): 7,
        ("Mission District", "North Beach"): 17,
        ("Mission District", "Embarcadero"): 19,
        ("Mission District", "Alamo Square"): 11,
        ("Mission District", "Nob Hill"): 12,
        ("Mission District", "Presidio"): 25,
        ("Mission District", "Fisherman's Wharf"): 22,
        ("Mission District", "Haight-Ashbury"): 12,
        ("Haight-Ashbury", "Union Square"): 19,
        ("Haight-Ashbury", "The Castro"): 6,
        ("Haight-Ashbury", "North Beach"): 19,
        ("Haight-Ashbury", "Embarcadero"): 20,
        ("Haight-Ashbury", "Alamo Square"): 5,
        ("Haight-Ashbury", "Nob Hill"): 15,
        ("Haight-Ashbury", "Presidio"): 15,
        ("Haight-Ashbury", "Fisherman's Wharf"): 23,
        ("Haight-Ashbury", "Mission District"): 11,
    }
    
    # Friend constraints
    friends = [
        {"name": "Melissa", "location": "The Castro", "start": "20:15", "end": "21:15", "min_duration": 30},
        {"name": "Kimberly", "location": "North Beach", "start": "7:00", "end": "10:30", "min_duration": 15},
        {"name": "Joseph", "location": "Embarcadero", "start": "15:30", "end": "19:30", "min_duration": 75},
        {"name": "Barbara", "location": "Alamo Square", "start": "20:45", "end": "21:45", "min_duration": 15},
        {"name": "Kenneth", "location": "Nob Hill", "start": "12:15", "end": "17:15", "min_duration": 105},
        {"name": "Joshua", "location": "Presidio", "start": "16:30", "end": "18:15", "min_duration": 105},
        {"name": "Brian", "location": "Fisherman's Wharf", "start": "9:30", "end": "15:30", "min_duration": 45},
        {"name": "Steven", "location": "Mission District", "start": "19:30", "end": "21:00", "min_duration": 90},
        {"name": "Betty", "location": "Haight-Ashbury", "start": "19:00", "end": "20:30", "min_duration": 90}
    ]
    
    # Convert time strings to minutes since 9:00
    def time_to_minutes(time_str):
        if ':' in time_str:
            hours, minutes = map(int, time_str.split(':'))
            return hours * 60 + minutes - 9 * 60  # Offset from 9:00
        return 0
    
    # Convert minutes to time string
    def minutes_to_time(minutes):
        total_minutes = 9 * 60 + minutes
        hours = total_minutes // 60
        mins = total_minutes % 60
        return f"{hours}:{mins:02d}"
    
    # Create problem
    problem = constraint.Problem()
    
    # Add variables for each friend (start time in minutes from 9:00)
    for friend in friends:
        start_min = time_to_minutes(friend["start"])
        end_min = time_to_minutes(friend["end"])
        problem.addVariable(f"{friend['name']}_start", range(start_min, end_min - friend["min_duration"] + 1))
        problem.addVariable(f"{friend['name']}_duration", [friend["min_duration"]])
    
    # Add constraint: meetings cannot overlap and must account for travel
    def no_overlap(*args):
        # Create list of meetings with start, end, and location
        meetings = []
        for i, friend in enumerate(friends):
            start = args[i * 2]
            duration = args[i * 2 + 1]
            end = start + duration
            meetings.append((start, end, friend["location"], friend["name"]))
        
        # Sort by start time
        meetings.sort()
        
        # Check for overlaps considering travel time
        for i in range(len(meetings) - 1):
            current_start, current_end, current_loc, current_name = meetings[i]
            next_start, next_end, next_loc, next_name = meetings[i + 1]
            
            # Check if next meeting starts before current ends (considering travel)
            travel_time = travel_times.get((current_loc, next_loc), 30)  # Default 30 min if not found
            if next_start < current_end + travel_time:
                return False
        
        return True
    
    # Add the constraint
    all_vars = []
    for friend in friends:
        all_vars.append(f"{friend['name']}_start")
        all_vars.append(f"{friend['name']}_duration")
    
    problem.addConstraint(no_overlap, all_vars)
    
    # Find a solution
    solutions = problem.getSolutions()
    
    if not solutions:
        # Fallback: try to schedule as many as possible
        # For simplicity, we'll use a greedy approach
        itinerary = []
        current_time = 0  # 9:00 in minutes from 9:00
        current_location = "Union Square"
        
        # Sort friends by end time
        sorted_friends = sorted(friends, key=lambda x: time_to_minutes(x["end"]))
        
        for friend in sorted_friends:
            start_min = time_to_minutes(friend["start"])
            end_min = time_to_minutes(friend["end"])
            min_duration = friend["min_duration"]
            
            # Calculate travel time
            travel_time = travel_times.get((current_location, friend["location"]), 30)
            
            # Earliest we can start after travel
            earliest_start = max(current_time + travel_time, start_min)
            
            # Check if we can fit the meeting
            if earliest_start + min_duration <= end_min:
                # Schedule the meeting
                itinerary.append({
                    "action": "meet",
                    "location": friend["location"],
                    "person": friend["name"],
                    "start_time": minutes_to_time(earliest_start),
                    "end_time": minutes_to_time(earliest_start + min_duration)
                })
                current_time = earliest_start + min_duration
                current_location = friend["location"]
        
        result = {"itinerary": itinerary}
    else:
        # Use the first solution found
        solution = solutions[0]
        itinerary = []
        
        # Create list of meetings
        meetings = []
        for friend in friends:
            start = solution[f"{friend['name']}_start"]
            duration = solution[f"{friend['name']}_duration"]
            meetings.append((start, friend["location"], friend["name"], duration))
        
        # Sort by start time
        meetings.sort()
        
        # Build itinerary
        for start, location, name, duration in meetings:
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": name,
                "start_time": minutes_to_time(start),
                "end_time": minutes_to_time(start + duration)
            })
        
        result = {"itinerary": itinerary}
    
    # Output as JSON
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()