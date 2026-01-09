import constraint
from datetime import datetime, timedelta
import json

def time_to_minutes(time_str):
    """Convert time string (H:MM) to minutes since midnight"""
    if isinstance(time_str, str):
        dt = datetime.strptime(time_str, "%H:%M")
    else:
        dt = time_str
    return dt.hour * 60 + dt.minute

def minutes_to_time(minutes):
    """Convert minutes since midnight to time string (H:MM)"""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    # Travel times in minutes (symmetric matrix)
    locations = ["Alamo Square", "Russian Hill", "Presidio", "Chinatown", 
                "Sunset District", "The Castro", "Embarcadero", "Golden Gate Park"]
    
    travel_times = {
        ("Alamo Square", "Russian Hill"): 13,
        ("Alamo Square", "Presidio"): 18,
        ("Alamo Square", "Chinatown"): 16,
        ("Alamo Square", "Sunset District"): 16,
        ("Alamo Square", "The Castro"): 8,
        ("Alamo Square", "Embarcadero"): 17,
        ("Alamo Square", "Golden Gate Park"): 9,
        ("Russian Hill", "Alamo Square"): 15,
        ("Russian Hill", "Presidio"): 14,
        ("Russian Hill", "Chinatown"): 9,
        ("Russian Hill", "Sunset District"): 23,
        ("Russian Hill", "The Castro"): 21,
        ("Russian Hill", "Embarcadero"): 8,
        ("Russian Hill", "Golden Gate Park"): 21,
        ("Presidio", "Alamo Square"): 18,
        ("Presidio", "Russian Hill"): 14,
        ("Presidio", "Chinatown"): 21,
        ("Presidio", "Sunset District"): 15,
        ("Presidio", "The Castro"): 21,
        ("Presidio", "Embarcadero"): 20,
        ("Presidio", "Golden Gate Park"): 12,
        ("Chinatown", "Alamo Square"): 17,
        ("Chinatown", "Russian Hill"): 7,
        ("Chinatown", "Presidio"): 19,
        ("Chinatown", "Sunset District"): 29,
        ("Chinatown", "The Castro"): 22,
        ("Chinatown", "Embarcadero"): 5,
        ("Chinatown", "Golden Gate Park"): 23,
        ("Sunset District", "Alamo Square"): 17,
        ("Sunset District", "Russian Hill"): 24,
        ("Sunset District", "Presidio"): 16,
        ("Sunset District", "Chinatown"): 30,
        ("Sunset District", "The Castro"): 17,
        ("Sunset District", "Embarcadero"): 31,
        ("Sunset District", "Golden Gate Park"): 11,
        ("The Castro", "Alamo Square"): 8,
        ("The Castro", "Russian Hill"): 18,
        ("The Castro", "Presidio"): 20,
        ("The Castro", "Chinatown"): 20,
        ("The Castro", "Sunset District"): 17,
        ("The Castro", "Embarcadero"): 22,
        ("The Castro", "Golden Gate Park"): 11,
        ("Embarcadero", "Alamo Square"): 19,
        ("Embarcadero", "Russian Hill"): 8,
        ("Embarcadero", "Presidio"): 20,
        ("Embarcadero", "Chinatown"): 7,
        ("Embarcadero", "Sunset District"): 30,
        ("Embarcadero", "The Castro"): 25,
        ("Embarcadero", "Golden Gate Park"): 25,
        ("Golden Gate Park", "Alamo Square"): 10,
        ("Golden Gate Park", "Russian Hill"): 19,
        ("Golden Gate Park", "Presidio"): 11,
        ("Golden Gate Park", "Chinatown"): 23,
        ("Golden Gate Park", "Sunset District"): 10,
        ("Golden Gate Park", "The Castro"): 13,
        ("Golden Gate Park", "Embarcadero"): 25,
    }
    
    # Friend constraints
    friends = {
        "Emily": {
            "location": "Russian Hill",
            "available_start": time_to_minutes("12:15"),
            "available_end": time_to_minutes("14:15"),
            "min_duration": 105
        },
        "Mark": {
            "location": "Presidio", 
            "available_start": time_to_minutes("14:45"),
            "available_end": time_to_minutes("19:30"),
            "min_duration": 60
        },
        "Deborah": {
            "location": "Chinatown",
            "available_start": time_to_minutes("7:30"), 
            "available_end": time_to_minutes("15:30"),
            "min_duration": 45
        },
        "Margaret": {
            "location": "Sunset District",
            "available_start": time_to_minutes("21:30"),
            "available_end": time_to_minutes("22:30"),
            "min_duration": 60
        },
        "George": {
            "location": "The Castro",
            "available_start": time_to_minutes("7:30"),
            "available_end": time_to_minutes("14:15"),
            "min_duration": 60
        },
        "Andrew": {
            "location": "Embarcadero",
            "available_start": time_to_minutes("20:15"),
            "available_end": time_to_minutes("22:00"),
            "min_duration": 75
        },
        "Steven": {
            "location": "Golden Gate Park",
            "available_start": time_to_minutes("11:15"),
            "available_end": time_to_minutes("21:15"),
            "min_duration": 105
        }
    }
    
    # Start at Alamo Square at 9:00
    current_time = time_to_minutes("9:00")
    current_location = "Alamo Square"
    
    problem = constraint.Problem()
    
    # Variables: start time and duration for each friend
    for friend in friends:
        info = friends[friend]
        available_duration = info["available_end"] - info["available_start"]
        max_duration = min(available_duration, 180)  # Cap at 3 hours max
        
        problem.addVariable(f"{friend}_start", range(info["available_start"], info["available_end"] + 1))
        problem.addVariable(f"{friend}_duration", range(info["min_duration"], max_duration + 1))
    
    # Constraint: meeting must fit within available window
    for friend in friends:
        info = friends[friend]
        def within_window(start, duration, friend_info=info):
            return start + duration <= friend_info["available_end"]
        problem.addConstraint(within_window, [f"{friend}_start", f"{friend}_duration"])
    
    # Constraint: meetings cannot overlap and must account for travel
    friend_list = list(friends.keys())
    
    # Create a closure to capture the friends dictionary and travel_times
    def make_no_overlap_constraint(f1_name, f2_name):
        def no_overlap_with_travel(f1_start, f1_dur, f2_start, f2_dur):
            f1_end = f1_start + f1_dur
            f2_end = f2_start + f2_dur
            
            loc1 = friends[f1_name]["location"]
            loc2 = friends[f2_name]["location"]
            travel_time = travel_times.get((loc1, loc2), travel_times.get((loc2, loc1), 30))
            
            # Either f1 ends before f2 starts (with travel time), or vice versa
            return (f1_end + travel_time <= f2_start) or (f2_end + travel_time <= f1_start)
        return no_overlap_with_travel
    
    for i in range(len(friend_list)):
        for j in range(i + 1, len(friend_list)):
            f1 = friend_list[i]
            f2 = friend_list[j]
            constraint_func = make_no_overlap_constraint(f1, f2)
            problem.addConstraint(constraint_func, 
                                [f"{f1}_start", f"{f1}_duration", f"{f2}_start", f"{f2}_duration"])
    
    # Objective: maximize total meeting time
    def objective(*args):
        total_time = 0
        for i, friend in enumerate(friend_list):
            total_time += args[i * 2 + 1]  # duration is at odd indices
        return total_time
    
    # Find solution that maximizes total meeting time
    solutions = problem.getSolutions()
    
    if not solutions:
        # Fallback: try to meet as many friends as possible with minimum durations
        best_solution = None
        best_score = -1
        
        for friend in friends:
            # Try meeting each friend individually with minimum duration
            info = friends[friend]
            start_time = max(current_time + travel_times.get((current_location, info["location"]), 30), 
                           info["available_start"])
            
            if start_time + info["min_duration"] <= info["available_end"]:
                score = info["min_duration"]
                if score > best_score:
                    best_score = score
                    best_solution = {
                        f"{friend}_start": start_time,
                        f"{friend}_duration": info["min_duration"]
                    }
        
        if best_solution:
            solution = best_solution
        else:
            # No meetings possible
            solution = {}
    else:
        # Find solution with maximum total meeting time
        best_solution = None
        best_score = -1
        
        for sol in solutions:
            score = objective(*[sol.get(f"{f}_{prop}", 0) for f in friend_list for prop in ["start", "duration"]])
            if score > best_score:
                best_score = score
                best_solution = sol
        
        solution = best_solution
    
    # Build itinerary
    itinerary = []
    
    if solution:
        # Create meeting events from solution
        meetings = []
        for friend in friends:
            if f"{friend}_start" in solution and f"{friend}_duration" in solution:
                start_time = solution[f"{friend}_start"]
                duration = solution[f"{friend}_duration"]
                location = friends[friend]["location"]
                
                meetings.append({
                    "person": friend,
                    "location": location,
                    "start": start_time,
                    "end": start_time + duration,
                    "duration": duration
                })
        
        # Sort meetings by start time
        meetings.sort(key=lambda x: x["start"])
        
        # Add meetings to itinerary
        for meeting in meetings:
            itinerary.append({
                "action": "meet",
                "location": meeting["location"],
                "person": meeting["person"],
                "start_time": minutes_to_time(meeting["start"]),
                "end_time": minutes_to_time(meeting["end"])
            })
    
    # Output result
    result = {
        "itinerary": itinerary
    }
    
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()