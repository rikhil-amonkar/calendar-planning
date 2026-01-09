import constraint
from datetime import datetime, timedelta
import json

def main():
    # Define locations
    locations = [
        "Presidio", "Marina District", "The Castro", "Fisherman's Wharf", 
        "Bayview", "Pacific Heights", "Mission District", "Alamo Square", "Golden Gate Park"
    ]
    
    # Travel time matrix (in minutes)
    travel_times = {
        "Presidio": {"Marina District": 11, "The Castro": 21, "Fisherman's Wharf": 19, 
                    "Bayview": 31, "Pacific Heights": 11, "Mission District": 26, 
                    "Alamo Square": 19, "Golden Gate Park": 12},
        "Marina District": {"Presidio": 10, "The Castro": 22, "Fisherman's Wharf": 10, 
                           "Bayview": 27, "Pacific Heights": 7, "Mission District": 20, 
                           "Alamo Square": 15, "Golden Gate Park": 18},
        "The Castro": {"Presidio": 20, "Marina District": 21, "Fisherman's Wharf": 24, 
                      "Bayview": 19, "Pacific Heights": 16, "Mission District": 7, 
                      "Alamo Square": 8, "Golden Gate Park": 11},
        "Fisherman's Wharf": {"Presidio": 17, "Marina District": 9, "The Castro": 27, 
                             "Bayview": 26, "Pacific Heights": 12, "Mission District": 22, 
                             "Alamo Square": 21, "Golden Gate Park": 25},
        "Bayview": {"Presidio": 32, "Marina District": 27, "The Castro": 19, 
                   "Fisherman's Wharf": 25, "Pacific Heights": 23, "Mission District": 13, 
                   "Alamo Square": 16, "Golden Gate Park": 22},
        "Pacific Heights": {"Presidio": 11, "Marina District": 6, "The Castro": 16, 
                           "Fisherman's Wharf": 13, "Bayview": 22, "Mission District": 15, 
                           "Alamo Square": 10, "Golden Gate Park": 15},
        "Mission District": {"Presidio": 25, "Marina District": 19, "The Castro": 7, 
                            "Fisherman's Wharf": 22, "Bayview": 14, "Pacific Heights": 16, 
                            "Alamo Square": 11, "Golden Gate Park": 17},
        "Alamo Square": {"Presidio": 17, "Marina District": 15, "The Castro": 8, 
                        "Fisherman's Wharf": 19, "Bayview": 16, "Pacific Heights": 10, 
                        "Mission District": 10, "Golden Gate Park": 9},
        "Golden Gate Park": {"Presidio": 11, "Marina District": 16, "The Castro": 13, 
                            "Fisherman's Wharf": 24, "Bayview": 23, "Pacific Heights": 16, 
                            "Mission District": 17, "Alamo Square": 9}
    }
    
    # Friend constraints
    friends = {
        "Amanda": {"location": "Marina District", "start": "14:45", "end": "19:30", "min_duration": 105},
        "Melissa": {"location": "The Castro", "start": "9:30", "end": "17:00", "min_duration": 30},
        "Jeffrey": {"location": "Fisherman's Wharf", "start": "12:45", "end": "18:45", "min_duration": 120},
        "Matthew": {"location": "Bayview", "start": "10:15", "end": "13:15", "min_duration": 30},
        "Nancy": {"location": "Pacific Heights", "start": "17:00", "end": "21:30", "min_duration": 105},
        "Karen": {"location": "Mission District", "start": "17:30", "end": "20:30", "min_duration": 105},
        "Robert": {"location": "Alamo Square", "start": "11:15", "end": "17:30", "min_duration": 120},
        "Joseph": {"location": "Golden Gate Park", "start": "8:30", "end": "21:15", "min_duration": 105}
    }
    
    # Convert time strings to minutes since 9:00
    def time_to_minutes(time_str):
        time_obj = datetime.strptime(time_str, "%H:%M")
        base_time = datetime.strptime("9:00", "%H:%M")
        delta = time_obj - base_time
        return int(delta.total_seconds() / 60)
    
    # Convert minutes to time string
    def minutes_to_time(minutes):
        base_time = datetime.strptime("9:00", "%H:%M")
        result_time = base_time + timedelta(minutes=minutes)
        return result_time.strftime("%H:%M")
    
    # Create problem
    problem = constraint.Problem()
    
    # Define variables for each friend: start time and duration
    friend_names = list(friends.keys())
    
    for friend in friend_names:
        friend_info = friends[friend]
        start_min = time_to_minutes(friend_info["start"])
        end_min = time_to_minutes(friend_info["end"])
        min_duration = friend_info["min_duration"]
        
        # Start time variable (in minutes from 9:00)
        problem.addVariable(f"{friend}_start", range(start_min, end_min - min_duration + 1))
        # Duration variable
        problem.addVariable(f"{friend}_duration", range(min_duration, end_min - start_min + 1))
    
    # Add constraints to ensure meetings don't overlap and account for travel
    def no_overlap_constraint(*args):
        # Extract start times and durations for all friends
        meetings = []
        for i in range(0, len(args), 2):
            start = args[i]
            duration = args[i + 1]
            end = start + duration
            meetings.append((start, end, friend_names[i // 2]))
        
        # Sort by start time
        meetings.sort()
        
        # Check for overlaps considering travel time
        for i in range(len(meetings) - 1):
            current_end = meetings[i][1]
            next_start = meetings[i + 1][0]
            current_friend = meetings[i][2]
            next_friend = meetings[i + 1][2]
            
            current_location = friends[current_friend]["location"]
            next_location = friends[next_friend]["location"]
            
            travel_time = travel_times[current_location][next_location]
            
            if current_end + travel_time > next_start:
                return False
        
        return True
    
    # Add the constraint
    all_vars = []
    for friend in friend_names:
        all_vars.append(f"{friend}_start")
        all_vars.append(f"{friend}_duration")
    
    problem.addConstraint(no_overlap_constraint, all_vars)
    
    # Define objective function: maximize total meeting time
    def objective_function(*args):
        total_duration = 0
        for i in range(1, len(args), 2):
            total_duration += args[i]
        return total_duration
    
    # Find solution
    solutions = problem.getSolutions()
    
    if not solutions:
        # Fallback: try to schedule as many friends as possible
        best_solution = None
        best_score = -1
        
        for friend_count in range(len(friend_names), 0, -1):
            # Reset problem
            problem = constraint.Problem()
            
            # Try to schedule friend_count friends
            for i, friend in enumerate(friend_names[:friend_count]):
                friend_info = friends[friend]
                start_min = time_to_minutes(friend_info["start"])
                end_min = time_to_minutes(friend_info["end"])
                min_duration = friend_info["min_duration"]
                
                problem.addVariable(f"{friend}_start", range(start_min, end_min - min_duration + 1))
                problem.addVariable(f"{friend}_duration", range(min_duration, end_min - start_min + 1))
            
            # Add constraints for the subset
            subset_vars = []
            for friend in friend_names[:friend_count]:
                subset_vars.append(f"{friend}_start")
                subset_vars.append(f"{friend}_duration")
            
            problem.addConstraint(no_overlap_constraint, subset_vars)
            
            solutions = problem.getSolutions()
            if solutions:
                # Find solution with maximum total duration
                for sol in solutions:
                    total_duration = 0
                    for friend in friend_names[:friend_count]:
                        total_duration += sol[f"{friend}_duration"]
                    
                    if total_duration > best_score:
                        best_score = total_duration
                        best_solution = sol
                        # Extend best_solution with zeros for unscheduled friends
                        for friend in friend_names[friend_count:]:
                            best_solution[f"{friend}_start"] = -1
                            best_solution[f"{friend}_duration"] = 0
                break
        
        if best_solution is None:
            # If still no solution, create a minimal schedule
            best_solution = {}
            for friend in friend_names:
                best_solution[f"{friend}_start"] = -1
                best_solution[f"{friend}_duration"] = 0
            
            # Schedule Joseph first (earliest availability)
            joseph_info = friends["Joseph"]
            start_min = time_to_minutes(joseph_info["start"])
            min_duration = joseph_info["min_duration"]
            best_solution["Joseph_start"] = start_min
            best_solution["Joseph_duration"] = min_duration
    else:
        # Find solution with maximum total duration
        best_solution = None
        best_score = -1
        for sol in solutions:
            total_duration = 0
            for friend in friend_names:
                total_duration += sol[f"{friend}_duration"]
            
            if total_duration > best_score:
                best_score = total_duration
                best_solution = sol
    
    # Build itinerary
    itinerary = []
    
    # Create list of scheduled meetings
    meetings = []
    for friend in friend_names:
        start = best_solution[f"{friend}_start"]
        duration = best_solution[f"{friend}_duration"]
        
        if start >= 0 and duration > 0:
            meetings.append({
                "friend": friend,
                "location": friends[friend]["location"],
                "start": start,
                "end": start + duration,
                "duration": duration
            })
    
    # Sort by start time
    meetings.sort(key=lambda x: x["start"])
    
    # Add travel from Presidio to first meeting
    if meetings:
        first_meeting = meetings[0]
        travel_start = 0  # Start from 9:00 at Presidio
        travel_end = travel_start + travel_times["Presidio"][first_meeting["location"]]
        
        itinerary.append({
            "action": "travel",
            "location": first_meeting["location"],
            "person": "",
            "start_time": minutes_to_time(travel_start),
            "end_time": minutes_to_time(travel_end)
        })
    
    # Add meetings and travel between them
    for i, meeting in enumerate(meetings):
        # Add meeting
        itinerary.append({
            "action": "meet",
            "location": meeting["location"],
            "person": meeting["friend"],
            "start_time": minutes_to_time(meeting["start"]),
            "end_time": minutes_to_time(meeting["end"])
        })
        
        # Add travel to next meeting if there is one
        if i < len(meetings) - 1:
            next_meeting = meetings[i + 1]
            travel_start = meeting["end"]
            travel_end = travel_start + travel_times[meeting["location"]][next_meeting["location"]]
            
            itinerary.append({
                "action": "travel",
                "location": next_meeting["location"],
                "person": "",
                "start_time": minutes_to_time(travel_start),
                "end_time": minutes_to_time(travel_end)
            })
    
    # Output result
    result = {
        "itinerary": itinerary
    }
    
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()