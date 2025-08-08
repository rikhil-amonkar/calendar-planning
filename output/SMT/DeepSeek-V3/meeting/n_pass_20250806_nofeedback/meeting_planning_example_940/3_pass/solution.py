from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 solver
    s = Solver()

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

    # Travel times dictionary (simplified)
    travel_times = {
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
        # Add other travel times as needed
    }

    # Function to convert time string to minutes
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    # Convert friends' availability to minutes
    for name, data in friends.items():
        data["start_min"] = time_to_minutes(data["start"])
        data["end_min"] = time_to_minutes(data["end"])

    # Create Z3 variables for each meeting
    meeting_vars = {}
    for name in friends:
        start_var = Int(f"start_{name}")
        end_var = Int(f"end_{name}")
        meeting_vars[name] = {"start": start_var, "end": end_var}

    # Add basic constraints for each meeting
    for name, data in friends.items():
        s.add(meeting_vars[name]["start"] >= data["start_min"])
        s.add(meeting_vars[name]["end"] <= data["end_min"])
        s.add(meeting_vars[name]["end"] == meeting_vars[name]["start"] + data["duration"])

    # Add constraints to prevent overlapping meetings
    for name1 in friends:
        for name2 in friends:
            if name1 != name2:
                s.add(Or(
                    meeting_vars[name1]["end"] <= meeting_vars[name2]["start"],
                    meeting_vars[name2]["end"] <= meeting_vars[name1]["start"]
                ))

    # Add travel time constraints between consecutive meetings
    # This is simplified - a better approach would track location changes
    # For now, we'll assume meetings are scheduled in order of availability
    sorted_names = sorted(friends.keys(), key=lambda x: friends[x]["start_min"])
    for i in range(len(sorted_names)-1):
        name1 = sorted_names[i]
        name2 = sorted_names[i+1]
        loc1 = friends[name1]["location"]
        loc2 = friends[name2]["location"]
        travel_time = travel_times.get((loc1, loc2), 0)
        s.add(meeting_vars[name2]["start"] >= meeting_vars[name1]["end"] + travel_time)

    # Starting at Union Square at 9:00 AM (540 minutes)
    s.add(meeting_vars[sorted_names[0]]["start"] >= 540 + travel_times.get(("Union Square", friends[sorted_names[0]]["location"]), 0))

    # Try to maximize number of meetings
    num_meetings = Int("num_meetings")
    s.add(num_meetings == sum([If(meeting_vars[name]["start"] >= 0, 1, 0) for name in friends]))
    maximize_num = num_meetings

    # Set optimization goal
    opt = Optimize()
    opt.add(s.assertions())
    opt.maximize(maximize_num)

    # Check if solution exists
    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        for name in friends:
            start_val = model[meeting_vars[name]["start"]]
            if is_int_value(start_val) and start_val.as_long() >= 0:
                start_time = start_val.as_long()
                end_time = model[meeting_vars[name]["end"]].as_long()
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": f"{start_time // 60:02d}:{start_time % 60:02d}",
                    "end_time": f"{end_time // 60:02d}:{end_time % 60:02d}"
                })
        # Sort by start time
        itinerary.sort(key=lambda x: time_to_minutes(x["start_time"]))
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid schedule found"}

# Solve the problem
solution = solve_scheduling_problem()

# Print the solution in JSON format
print(json.dumps(solution, indent=2))