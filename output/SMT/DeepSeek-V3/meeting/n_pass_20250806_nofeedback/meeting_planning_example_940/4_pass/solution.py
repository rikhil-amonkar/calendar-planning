from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 solver with optimization
    opt = Optimize()

    # Define friends and their availability
    friends = {
        "Kevin": {"location": "Mission District", "start": "20:45", "end": "21:45", "duration": 60},
        "Mark": {"location": "Fisherman's Wharf", "start": "17:15", "end": "20:00", "duration": 90},
        "Jessica": {"location": "Russian Hill", "start": "09:00", "end": "15:00", "duration": 120},
        "Jason": {"location": "Marina District", "start": "15:15", "end": "21:45", "duration": 120},
        "John": {"location": "North Beach", "start": "09:45", "end": "18:00", "duration": 15},
        "Karen": {"location": "Chinatown", "start": "16:45", "end": "19:00", "duration": 75},
        "Sarah": {"location": "Pacific Heights", "start": "17:30", "end": "18:15", "duration": 45},
        "Amanda": {"location": "The Castro", "start": "20:00", "end": "21:15", "duration": 60},
        "Nancy": {"location": "Nob Hill", "start": "09:45", "end": "13:00", "duration": 45},
        "Rebecca": {"location": "Sunset District", "start": "08:45", "end": "15:00", "duration": 75}
    }

    # Complete travel times matrix
    locations = list(set(f["location"] for f in friends.values())) + ["Union Square"]
    travel_times = {}
    for loc1 in locations:
        for loc2 in locations:
            if loc1 == loc2:
                travel_times[(loc1, loc2)] = 0
            else:
                # Use default travel time if specific not available
                travel_times[(loc1, loc2)] = 20  # Default travel time

    # Update with known travel times
    known_times = {
        ("Union Square", "Mission District"): 14,
        ("Union Square", "Fisherman's Wharf"): 15,
        ("Union Square", "Russian Hill"): 13,
        ("Union Square", "Marina District"): 18,
        ("Union Square", "North Beach"): 10,
        ("Union Square", "Chinatown"): 7,
        ("Union Square", "Pacific Heights"): 15,
        ("Union Square", "The Castro"): 17,
        ("Union Square", "Nob Hill"): 9,
        ("Union Square", "Sunset District"): 27,
    }
    travel_times.update(known_times)
    # Add reverse directions
    for (loc1, loc2), time in known_times.items():
        travel_times[(loc2, loc1)] = time

    # Helper function to convert time to minutes
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    # Convert availability windows to minutes
    for name, data in friends.items():
        data["start_min"] = time_to_minutes(data["start"])
        data["end_min"] = time_to_minutes(data["end"])

    # Create Z3 variables
    meeting_vars = {}
    for name in friends:
        start_var = Int(f"start_{name}")
        end_var = Int(f"end_{name}")
        meeting_vars[name] = {"start": start_var, "end": end_var, "scheduled": Bool(f"scheduled_{name}")}

    # Basic meeting constraints
    for name, data in friends.items():
        opt.add(Implies(meeting_vars[name]["scheduled"], 
                       And(meeting_vars[name]["start"] >= data["start_min"],
                           meeting_vars[name]["end"] <= data["end_min"],
                           meeting_vars[name]["end"] == meeting_vars[name]["start"] + data["duration"])))

    # Sequence variables to model meeting order
    sequence = [Int(f"seq_{i}") for i in range(len(friends))]
    opt.add(Distinct(sequence))
    for i in range(len(friends)):
        opt.add(sequence[i] >= 0)
        opt.add(sequence[i] < len(friends))

    # Travel time constraints between consecutive meetings
    for i in range(len(friends)-1):
        current = sequence[i]
        next_ = sequence[i+1]
        
        # Get current and next meeting names
        current_name = [name for name in friends][current]
        next_name = [name for name in friends][next_]
        
        # Add travel time constraint
        loc1 = friends[current_name]["location"]
        loc2 = friends[next_name]["location"]
        travel_time = travel_times[(loc1, loc2)]
        
        opt.add(Implies(And(meeting_vars[current_name]["scheduled"], meeting_vars[next_name]["scheduled"]),
                       meeting_vars[next_name]["start"] >= meeting_vars[current_name]["end"] + travel_time))

    # Starting point constraint
    first_meeting = sequence[0]
    first_name = [name for name in friends][first_meeting]
    start_loc = "Union Square"
    start_time = time_to_minutes("09:00")
    travel_time = travel_times[(start_loc, friends[first_name]["location"])]
    opt.add(Implies(meeting_vars[first_name]["scheduled"],
                   meeting_vars[first_name]["start"] >= start_time + travel_time))

    # Maximize number of scheduled meetings
    num_scheduled = Sum([If(meeting_vars[name]["scheduled"], 1, 0) for name in friends])
    opt.maximize(num_scheduled)

    # Solve the problem
    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        scheduled_meetings = []
        
        # Collect scheduled meetings
        for name in friends:
            if is_true(model[meeting_vars[name]["scheduled"]]):
                start = model[meeting_vars[name]["start"]].as_long()
                end = model[meeting_vars[name]["end"]].as_long()
                scheduled_meetings.append({
                    "name": name,
                    "start": start,
                    "end": end
                })
        
        # Sort by start time
        scheduled_meetings.sort(key=lambda x: x["start"])
        
        # Format output
        for meeting in scheduled_meetings:
            itinerary.append({
                "action": "meet",
                "person": meeting["name"],
                "start_time": f"{meeting['start'] // 60:02d}:{meeting['start'] % 60:02d}",
                "end_time": f"{meeting['end'] // 60:02d}:{meeting['end'] % 60:02d}"
            })
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid schedule found"}

# Solve and print the solution
solution = solve_scheduling_problem()
print(json.dumps(solution, indent=2))