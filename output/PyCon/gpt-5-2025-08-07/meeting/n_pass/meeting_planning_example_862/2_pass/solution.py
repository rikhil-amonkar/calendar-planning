import constraint
from datetime import datetime, timedelta
import json

def main():
    # Define all locations
    locations = [
        "Mission District", "Alamo Square", "Presidio", "Russian Hill", "North Beach",
        "Golden Gate Park", "Richmond District", "Embarcadero", "Financial District", "Marina District"
    ]
    
    # Travel time matrix (minutes)
    travel_times = {
        ("Mission District", "Alamo Square"): 11,
        ("Mission District", "Presidio"): 25,
        ("Mission District", "Russian Hill"): 15,
        ("Mission District", "North Beach"): 17,
        ("Mission District", "Golden Gate Park"): 17,
        ("Mission District", "Richmond District"): 20,
        ("Mission District", "Embarcadero"): 19,
        ("Mission District", "Financial District"): 15,
        ("Mission District", "Marina District"): 19,
        ("Alamo Square", "Mission District"): 10,
        ("Alamo Square", "Presidio"): 17,
        ("Alamo Square", "Russian Hill"): 13,
        ("Alamo Square", "North Beach"): 15,
        ("Alamo Square", "Golden Gate Park"): 9,
        ("Alamo Square", "Richmond District"): 11,
        ("Alamo Square", "Embarcadero"): 16,
        ("Alamo Square", "Financial District"): 17,
        ("Alamo Square", "Marina District"): 15,
        ("Presidio", "Mission District"): 26,
        ("Presidio", "Alamo Square"): 19,
        ("Presidio", "Russian Hill"): 14,
        ("Presidio", "North Beach"): 18,
        ("Presidio", "Golden Gate Park"): 12,
        ("Presidio", "Richmond District"): 7,
        ("Presidio", "Embarcadero"): 20,
        ("Presidio", "Financial District"): 23,
        ("Presidio", "Marina District"): 11,
        ("Russian Hill", "Mission District"): 16,
        ("Russian Hill", "Alamo Square"): 15,
        ("Russian Hill", "Presidio"): 14,
        ("Russian Hill", "North Beach"): 5,
        ("Russian Hill", "Golden Gate Park"): 21,
        ("Russian Hill", "Richmond District"): 14,
        ("Russian Hill", "Embarcadero"): 8,
        ("Russian Hill", "Financial District"): 11,
        ("Russian Hill", "Marina District"): 7,
        ("North Beach", "Mission District"): 18,
        ("North Beach", "Alamo Square"): 16,
        ("North Beach", "Presidio"): 17,
        ("North Beach", "Russian Hill"): 4,
        ("North Beach", "Golden Gate Park"): 22,
        ("North Beach", "Richmond District"): 18,
        ("North Beach", "Embarcadero"): 6,
        ("North Beach", "Financial District"): 8,
        ("North Beach", "Marina District"): 9,
        ("Golden Gate Park", "Mission District"): 17,
        ("Golden Gate Park", "Alamo Square"): 9,
        ("Golden Gate Park", "Presidio"): 11,
        ("Golden Gate Park", "Russian Hill"): 19,
        ("Golden Gate Park", "North Beach"): 23,
        ("Golden Gate Park", "Richmond District"): 7,
        ("Golden Gate Park", "Embarcadero"): 25,
        ("Golden Gate Park", "Financial District"): 26,
        ("Golden Gate Park", "Marina District"): 16,
        ("Richmond District", "Mission District"): 20,
        ("Richmond District", "Alamo Square"): 13,
        ("Richmond District", "Presidio"): 7,
        ("Richmond District", "Russian Hill"): 13,
        ("Richmond District", "North Beach"): 17,
        ("Richmond District", "Golden Gate Park"): 9,
        ("Richmond District", "Embarcadero"): 19,
        ("Richmond District", "Financial District"): 22,
        ("Richmond District", "Marina District"): 9,
        ("Embarcadero", "Mission District"): 20,
        ("Embarcadero", "Alamo Square"): 19,
        ("Embarcadero", "Presidio"): 20,
        ("Embarcadero", "Russian Hill"): 8,
        ("Embarcadero", "North Beach"): 5,
        ("Embarcadero", "Golden Gate Park"): 25,
        ("Embarcadero", "Richmond District"): 21,
        ("Embarcadero", "Financial District"): 5,
        ("Embarcadero", "Marina District"): 12,
        ("Financial District", "Mission District"): 17,
        ("Financial District", "Alamo Square"): 17,
        ("Financial District", "Presidio"): 22,
        ("Financial District", "Russian Hill"): 11,
        ("Financial District", "North Beach"): 7,
        ("Financial District", "Golden Gate Park"): 23,
        ("Financial District", "Richmond District"): 21,
        ("Financial District", "Embarcadero"): 4,
        ("Financial District", "Marina District"): 15,
        ("Marina District", "Mission District"): 20,
        ("Marina District", "Alamo Square"): 15,
        ("Marina District", "Presidio"): 10,
        ("Marina District", "Russian Hill"): 8,
        ("Marina District", "North Beach"): 11,
        ("Marina District", "Golden Gate Park"): 18,
        ("Marina District", "Richmond District"): 11,
        ("Marina District", "Embarcadero"): 14,
        ("Marina District", "Financial District"): 17,
    }
    
    # Friend constraints
    friends = [
        {"name": "Laura", "location": "Alamo Square", "available_start": "14:30", "available_end": "16:15", "min_duration": 75},
        {"name": "Brian", "location": "Presidio", "available_start": "10:15", "available_end": "17:00", "min_duration": 30},
        {"name": "Karen", "location": "Russian Hill", "available_start": "18:00", "available_end": "20:15", "min_duration": 90},
        {"name": "Stephanie", "location": "North Beach", "available_start": "10:15", "available_end": "16:00", "min_duration": 75},
        {"name": "Helen", "location": "Golden Gate Park", "available_start": "11:30", "available_end": "21:45", "min_duration": 120},
        {"name": "Sandra", "location": "Richmond District", "available_start": "8:00", "available_end": "15:15", "min_duration": 30},
        {"name": "Mary", "location": "Embarcadero", "available_start": "16:45", "available_end": "18:45", "min_duration": 120},
        {"name": "Deborah", "location": "Financial District", "available_start": "19:00", "available_end": "20:45", "min_duration": 105},
        {"name": "Elizabeth", "location": "Marina District", "available_start": "8:30", "available_end": "13:15", "min_duration": 105}
    ]
    
    # Convert time strings to minutes since 9:00
    def time_to_minutes(time_str):
        if isinstance(time_str, str):
            dt = datetime.strptime(time_str, "%H:%M")
            base = datetime.strptime("9:00", "%H:%M")
            return int((dt - base).total_seconds() / 60)
        return time_str
    
    # Convert minutes since 9:00 back to time string
    def minutes_to_time(minutes):
        base = datetime.strptime("9:00", "%H:%M")
        new_time = base + timedelta(minutes=minutes)
        return new_time.strftime("%H:%M").lstrip('0')
    
    # Create problem
    problem = constraint.Problem()
    
    # Variables: start time for each friend meeting (in minutes since 9:00)
    friend_vars = {}
    for friend in friends:
        name = friend["name"]
        available_start = time_to_minutes(friend["available_start"])
        available_end = time_to_minutes(friend["available_end"])
        min_duration = friend["min_duration"]
        
        # Meeting must start between available_start and available_end - min_duration
        problem.addVariable(f"{name}_start", range(available_start, available_end - min_duration + 1))
        
        # For end time, we'll use a constraint instead of a separate variable
        # We'll calculate end time from start time later
    
    # Add constraint for end time calculation
    for friend in friends:
        name = friend["name"]
        min_duration = friend["min_duration"]
        
        def end_time_constraint(start, fd=friend):
            return start + fd["min_duration"]
        
        problem.addConstraint(end_time_constraint, [f"{name}_start", f"{name}_end"])
    
    # Add travel time constraints
    for i, friend1 in enumerate(friends):
        for j, friend2 in enumerate(friends):
            if i != j:
                loc1 = friend1["location"]
                loc2 = friend2["location"]
                travel_time = travel_times.get((loc1, loc2), 30)  # Default to 30 if not found
                
                # If we meet friend1 before friend2, ensure enough travel time
                def travel_constraint(end1, start2, travel=travel_time):
                    return start2 >= end1 + travel
                
                problem.addConstraint(travel_constraint, 
                                    [f"{friend1['name']}_end", f"{friend2['name']}_start"])
    
    # Start from Mission District at 9:00
    first_friend_start_vars = [f"{friend['name']}_start" for friend in friends]
    
    def first_meeting_constraint(*starts):
        # At least one meeting should start after travel time from Mission District
        mission_start = 0  # 9:00 in our time system
        valid_starts = [s for s in starts if s >= mission_start + 10]  # Assume min travel 10 min
        return len(valid_starts) > 0
    
    problem.addConstraint(first_meeting_constraint, first_friend_start_vars)
    
    # Try to find a solution
    solution = problem.getSolution()
    
    if solution:
        # Create itinerary
        itinerary = []
        
        # Collect all meetings with their times
        meetings = []
        for friend in friends:
            name = friend["name"]
            start_time = solution[f"{name}_start"]
            end_time = solution[f"{name}_end"]
            meetings.append({
                "person": name,
                "location": friend["location"],
                "start": start_time,
                "end": end_time
            })
        
        # Sort meetings by start time
        meetings.sort(key=lambda x: x["start"])
        
        # Add travel from Mission District to first meeting
        first_meeting = meetings[0]
        travel_from_mission = travel_times.get(("Mission District", first_meeting["location"]), 15)
        
        # Convert to final itinerary format
        for meeting in meetings:
            itinerary.append({
                "action": "meet",
                "location": meeting["location"],
                "person": meeting["person"],
                "start_time": minutes_to_time(meeting["start"]),
                "end_time": minutes_to_time(meeting["end"])
            })
        
        # Output as JSON
        result = {
            "itinerary": itinerary
        }
        
        print(json.dumps(result, indent=2))
    else:
        # If no solution found, create a fallback schedule
        print(json.dumps({"itinerary": []}, indent=2))

if __name__ == "__main__":
    main()