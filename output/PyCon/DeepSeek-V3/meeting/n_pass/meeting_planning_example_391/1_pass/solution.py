import constraint
from datetime import datetime, timedelta
import json

def time_to_minutes(time_str):
    """Convert time string (H:MM) to minutes since midnight"""
    dt = datetime.strptime(time_str, '%H:%M')
    return dt.hour * 60 + dt.minute

def minutes_to_time(minutes):
    """Convert minutes since midnight to time string (H:MM)"""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    # Travel times in minutes (symmetric matrix representation)
    locations = ["Sunset District", "Alamo Square", "Russian Hill", "Presidio", "Financial District"]
    travel_times = {
        ("Sunset District", "Alamo Square"): 17,
        ("Sunset District", "Russian Hill"): 24,
        ("Sunset District", "Presidio"): 16,
        ("Sunset District", "Financial District"): 30,
        ("Alamo Square", "Sunset District"): 16,
        ("Alamo Square", "Russian Hill"): 13,
        ("Alamo Square", "Presidio"): 18,
        ("Alamo Square", "Financial District"): 17,
        ("Russian Hill", "Sunset District"): 23,
        ("Russian Hill", "Alamo Square"): 15,
        ("Russian Hill", "Presidio"): 14,
        ("Russian Hill", "Financial District"): 11,
        ("Presidio", "Sunset District"): 15,
        ("Presidio", "Alamo Square"): 18,
        ("Presidio", "Russian Hill"): 14,
        ("Presidio", "Financial District"): 23,
        ("Financial District", "Sunset District"): 31,
        ("Financial District", "Alamo Square"): 17,
        ("Financial District", "Russian Hill"): 10,
        ("Financial District", "Presidio"): 22,
    }
    
    # Person constraints
    people = {
        "Kevin": {
            "location": "Alamo Square",
            "available_start": time_to_minutes("8:15"),
            "available_end": time_to_minutes("21:30"),
            "min_duration": 75
        },
        "Kimberly": {
            "location": "Russian Hill", 
            "available_start": time_to_minutes("8:45"),
            "available_end": time_to_minutes("12:30"),
            "min_duration": 30
        },
        "Joseph": {
            "location": "Presidio",
            "available_start": time_to_minutes("18:30"),
            "available_end": time_to_minutes("19:15"),
            "min_duration": 45
        },
        "Thomas": {
            "location": "Financial District",
            "available_start": time_to_minutes("19:00"),
            "available_end": time_to_minutes("21:45"),
            "min_duration": 45
        }
    }
    
    # Start at Sunset District at 9:00 AM
    start_time = time_to_minutes("9:00")
    start_location = "Sunset District"
    
    # Create problem
    problem = constraint.Problem()
    
    # Variables: start time for each person (in minutes since midnight)
    person_names = list(people.keys())
    for person in person_names:
        person_info = people[person]
        problem.addVariable(f"{person}_start", 
                           range(person_info["available_start"], 
                                 person_info["available_end"] - person_info["min_duration"] + 1))
    
    # Calculate all possible orders
    from itertools import permutations
    best_schedule = None
    max_meetings = 0
    
    # Try different visit orders
    for order in permutations(person_names):
        current_time = start_time
        current_location = start_location
        schedule = []
        valid_schedule = True
        
        for person in order:
            person_info = people[person]
            target_location = person_info["location"]
            
            # Travel time
            travel_time = travel_times.get((current_location, target_location), 
                                          travel_times.get((target_location, current_location), 0))
            
            # Arrival time at meeting
            arrival_time = current_time + travel_time
            
            # Check if we can meet within their availability
            if arrival_time > person_info["available_end"] - person_info["min_duration"]:
                valid_schedule = False
                break
                
            # Start meeting at earliest possible time
            meeting_start = max(arrival_time, person_info["available_start"])
            meeting_end = meeting_start + person_info["min_duration"]
            
            # Check if meeting fits in availability window
            if meeting_end > person_info["available_end"]:
                valid_schedule = False
                break
                
            # Add to schedule
            schedule.append({
                "person": person,
                "location": target_location,
                "start_time": minutes_to_time(meeting_start),
                "end_time": minutes_to_time(meeting_end)
            })
            
            # Update current time and location
            current_time = meeting_end
            current_location = target_location
        
        # Check if this schedule is better
        if valid_schedule and len(schedule) > max_meetings:
            max_meetings = len(schedule)
            best_schedule = schedule
    
    # If no valid schedule found with all meetings, try subsets
    if best_schedule is None:
        for num_meetings in range(len(person_names), 0, -1):
            for order in permutations(person_names, num_meetings):
                current_time = start_time
                current_location = start_location
                schedule = []
                valid_schedule = True
                
                for person in order:
                    person_info = people[person]
                    target_location = person_info["location"]
                    
                    # Travel time
                    travel_time = travel_times.get((current_location, target_location), 
                                                  travel_times.get((target_location, current_location), 0))
                    
                    # Arrival time at meeting
                    arrival_time = current_time + travel_time
                    
                    # Check if we can meet within their availability
                    if arrival_time > person_info["available_end"] - person_info["min_duration"]:
                        valid_schedule = False
                        break
                        
                    # Start meeting at earliest possible time
                    meeting_start = max(arrival_time, person_info["available_start"])
                    meeting_end = meeting_start + person_info["min_duration"]
                    
                    # Check if meeting fits in availability window
                    if meeting_end > person_info["available_end"]:
                        valid_schedule = False
                        break
                        
                    # Add to schedule
                    schedule.append({
                        "person": person,
                        "location": target_location,
                        "start_time": minutes_to_time(meeting_start),
                        "end_time": minutes_to_time(meeting_end)
                    })
                    
                    # Update current time and location
                    current_time = meeting_end
                    current_location = target_location
                
                if valid_schedule:
                    best_schedule = schedule
                    break
            if best_schedule is not None:
                break
    
    # Format output
    if best_schedule:
        itinerary = []
        for meeting in best_schedule:
            itinerary.append({
                "action": "meet",
                "location": meeting["location"],
                "person": meeting["person"],
                "start_time": meeting["start_time"],
                "end_time": meeting["end_time"]
            })
        
        result = {"itinerary": itinerary}
    else:
        result = {"itinerary": []}
    
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()