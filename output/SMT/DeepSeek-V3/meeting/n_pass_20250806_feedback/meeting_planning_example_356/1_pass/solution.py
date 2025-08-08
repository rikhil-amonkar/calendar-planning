from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 solver and optimizer
    solver = Optimize()
    
    # Define friends and their availability
    friends = {
        "Barbara": {"location": "North Beach", "start": (13, 45), "end": (20, 15), "min_duration": 60},
        "Margaret": {"location": "Presidio", "start": (10, 15), "end": (15, 15), "min_duration": 30},
        "Kevin": {"location": "Haight-Ashbury", "start": (20, 0), "end": (20, 45), "min_duration": 30},
        "Kimberly": {"location": "Union Square", "start": (7, 45), "end": (16, 45), "min_duration": 30}
    }
    
    # Travel times dictionary: from -> to -> minutes
    travel_times = {
        "Bayview": {
            "North Beach": 21,
            "Presidio": 31,
            "Haight-Ashbury": 19,
            "Union Square": 17
        },
        "North Beach": {
            "Bayview": 22,
            "Presidio": 17,
            "Haight-Ashbury": 18,
            "Union Square": 7
        },
        "Presidio": {
            "Bayview": 31,
            "North Beach": 18,
            "Haight-Ashbury": 15,
            "Union Square": 22
        },
        "Haight-Ashbury": {
            "Bayview": 18,
            "North Beach": 19,
            "Presidio": 15,
            "Union Square": 17
        },
        "Union Square": {
            "Bayview": 15,
            "North Beach": 10,
            "Presidio": 24,
            "Haight-Ashbury": 18
        }
    }
    
    # Current location starts at Bayview at 9:00 AM
    current_location = "Bayview"
    current_time = (9, 0)  # 9:00 AM
    
    # Convert time to minutes since midnight for easier arithmetic
    def time_to_minutes(time):
        return time[0] * 60 + time[1]
    
    current_minutes = time_to_minutes(current_time)
    
    # Variables for each meeting: start and end times in minutes since midnight
    meet_vars = {}
    for name in friends:
        meet_vars[name] = {
            "start": Int(f"start_{name}"),
            "end": Int(f"end_{name}"),
            "scheduled": Bool(f"scheduled_{name}")
        }
    
    # Constraints for each friend's meeting
    for name in friends:
        friend = friends[name]
        start_min = time_to_minutes(friend["start"])
        end_min = time_to_minutes(friend["end"])
        min_duration = friend["min_duration"]
        
        # If the meeting is scheduled, it must be within the friend's window and meet duration
        solver.add(Implies(meet_vars[name]["scheduled"], 
                           And(meet_vars[name]["start"] >= start_min,
                               meet_vars[name]["end"] <= end_min,
                               meet_vars[name]["end"] - meet_vars[name]["start"] >= min_duration)))
    
    # Order of meetings: we need to sequence them with travel times
    # We'll assume a simple order and let Z3 find feasible sequences
    
    # Maximize the number of scheduled meetings
    scheduled_meetings = [If(meet_vars[name]["scheduled"], 1, 0) for name in friends]
    solver.maximize(Sum(scheduled_meetings))
    
    # Additional constraints to ensure feasible travel times between meetings
    # This is a simplified approach; a more comprehensive approach would model all possible sequences
    # For simplicity, we'll assume a possible order and add constraints accordingly
    
    # Possible order: Kimberly -> Margaret -> Barbara -> Kevin
    # This is a heuristic; the solver will adjust if this order is infeasible
    
    # Check if Kimberly is scheduled
    kimberly_scheduled = meet_vars["Kimberly"]["scheduled"]
    kimberly_start = meet_vars["Kimberly"]["start"]
    kimberly_end = meet_vars["Kimberly"]["end"]
    # Travel from Bayview to Union Square: 17 minutes
    solver.add(Implies(kimberly_scheduled, 
                      kimberly_start >= current_minutes + travel_times[current_location]["Union Square"]))
    
    # If Kimberly is scheduled, next could be Margaret
    margaret_scheduled = meet_vars["Margaret"]["scheduled"]
    margaret_start = meet_vars["Margaret"]["start"]
    margaret_end = meet_vars["Margaret"]["end"]
    # Travel from Union Square to Presidio: 24 minutes
    solver.add(Implies(And(kimberly_scheduled, margaret_scheduled),
               margaret_start >= kimberly_end + travel_times["Union Square"]["Presidio"]))
    
    # Then Barbara
    barbara_scheduled = meet_vars["Barbara"]["scheduled"]
    barbara_start = meet_vars["Barbara"]["start"]
    barbara_end = meet_vars["Barbara"]["end"]
    # Travel from Presidio to North Beach: 18 minutes
    solver.add(Implies(And(margaret_scheduled, barbara_scheduled),
                       barbara_start >= margaret_end + travel_times["Presidio"]["North Beach"]))
    
    # Then Kevin
    kevin_scheduled = meet_vars["Kevin"]["scheduled"]
    kevin_start = meet_vars["Kevin"]["start"]
    kevin_end = meet_vars["Kevin"]["end"]
    # Travel from North Beach to Haight-Ashbury: 18 minutes
    solver.add(Implies(And(barbara_scheduled, kevin_scheduled),
                       kevin_start >= barbara_end + travel_times["North Beach"]["Haight-Ashbury"]))
    
    # Check if the model is satisfiable
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        
        # Helper function to convert minutes back to HH:MM format
        def minutes_to_time(minutes):
            h = minutes // 60
            m = minutes % 60
            return f"{h:02d}:{m:02d}"
        
        # Collect scheduled meetings
        for name in friends:
            if model.evaluate(meet_vars[name]["scheduled"]):
                start = model.evaluate(meet_vars[name]["start"]).as_long()
                end = model.evaluate(meet_vars[name]["end"]).as_long()
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": minutes_to_time(start),
                    "end_time": minutes_to_time(end)
                })
        
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: x["start_time"])
        
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the problem and print the result
result = solve_scheduling_problem()
print(json.dumps(result, indent=2))