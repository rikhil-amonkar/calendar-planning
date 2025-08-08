from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 solver with optimization
    s = Optimize()

    # Define the friends and their availability
    friends = {
        "Mark": {"location": "Marina District", "start": (18, 45), "end": (21, 0), "min_duration": 90},
        "Karen": {"location": "Financial District", "start": (9, 30), "end": (12, 45), "min_duration": 90},
        "Barbara": {"location": "Alamo Square", "start": (10, 0), "end": (19, 30), "min_duration": 90},
        "Nancy": {"location": "Golden Gate Park", "start": (16, 45), "end": (20, 0), "min_duration": 105},
        "David": {"location": "The Castro", "start": (9, 0), "end": (18, 0), "min_duration": 120},
        "Linda": {"location": "Bayview", "start": (18, 15), "end": (19, 45), "min_duration": 45},
        "Kevin": {"location": "Sunset District", "start": (10, 0), "end": (17, 45), "min_duration": 120},
        "Matthew": {"location": "Haight-Ashbury", "start": (10, 15), "end": (15, 30), "min_duration": 45},
        "Andrew": {"location": "Nob Hill", "start": (11, 45), "end": (16, 45), "min_duration": 105}
    }

    # Define travel times between locations (in minutes)
    travel_times = {
        ("Russian Hill", "Marina District"): 7,
        ("Russian Hill", "Financial District"): 11,
        ("Russian Hill", "Alamo Square"): 15,
        ("Russian Hill", "Golden Gate Park"): 21,
        ("Russian Hill", "The Castro"): 21,
        ("Russian Hill", "Bayview"): 23,
        ("Russian Hill", "Sunset District"): 23,
        ("Russian Hill", "Haight-Ashbury"): 17,
        ("Russian Hill", "Nob Hill"): 5,
        ("Marina District", "Russian Hill"): 8,
        ("Marina District", "Financial District"): 17,
        ("Marina District", "Alamo Square"): 15,
        ("Marina District", "Golden Gate Park"): 18,
        ("Marina District", "The Castro"): 22,
        ("Marina District", "Bayview"): 27,
        ("Marina District", "Sunset District"): 19,
        ("Marina District", "Haight-Ashbury"): 16,
        ("Marina District", "Nob Hill"): 12,
        ("Financial District", "Russian Hill"): 11,
        ("Financial District", "Marina District"): 15,
        ("Financial District", "Alamo Square"): 17,
        ("Financial District", "Golden Gate Park"): 23,
        ("Financial District", "The Castro"): 20,
        ("Financial District", "Bayview"): 19,
        ("Financial District", "Sunset District"): 30,
        ("Financial District", "Haight-Ashbury"): 19,
        ("Financial District", "Nob Hill"): 8,
        ("Alamo Square", "Russian Hill"): 13,
        ("Alamo Square", "Marina District"): 15,
        ("Alamo Square", "Financial District"): 17,
        ("Alamo Square", "Golden Gate Park"): 9,
        ("Alamo Square", "The Castro"): 8,
        ("Alamo Square", "Bayview"): 16,
        ("Alamo Square", "Sunset District"): 16,
        ("Alamo Square", "Haight-Ashbury"): 5,
        ("Alamo Square", "Nob Hill"): 11,
        ("Golden Gate Park", "Russian Hill"): 19,
        ("Golden Gate Park", "Marina District"): 16,
        ("Golden Gate Park", "Financial District"): 26,
        ("Golden Gate Park", "Alamo Square"): 9,
        ("Golden Gate Park", "The Castro"): 13,
        ("Golden Gate Park", "Bayview"): 23,
        ("Golden Gate Park", "Sunset District"): 10,
        ("Golden Gate Park", "Haight-Ashbury"): 7,
        ("Golden Gate Park", "Nob Hill"): 20,
        ("The Castro", "Russian Hill"): 18,
        ("The Castro", "Marina District"): 21,
        ("The Castro", "Financial District"): 21,
        ("The Castro", "Alamo Square"): 8,
        ("The Castro", "Golden Gate Park"): 11,
        ("The Castro", "Bayview"): 19,
        ("The Castro", "Sunset District"): 17,
        ("The Castro", "Haight-Ashbury"): 6,
        ("The Castro", "Nob Hill"): 16,
        ("Bayview", "Russian Hill"): 23,
        ("Bayview", "Marina District"): 27,
        ("Bayview", "Financial District"): 19,
        ("Bayview", "Alamo Square"): 16,
        ("Bayview", "Golden Gate Park"): 22,
        ("Bayview", "The Castro"): 19,
        ("Bayview", "Sunset District"): 23,
        ("Bayview", "Haight-Ashbury"): 19,
        ("Bayview", "Nob Hill"): 20,
        ("Sunset District", "Russian Hill"): 24,
        ("Sunset District", "Marina District"): 21,
        ("Sunset District", "Financial District"): 30,
        ("Sunset District", "Alamo Square"): 17,
        ("Sunset District", "Golden Gate Park"): 11,
        ("Sunset District", "The Castro"): 17,
        ("Sunset District", "Bayview"): 22,
        ("Sunset District", "Haight-Ashbury"): 15,
        ("Sunset District", "Nob Hill"): 27,
        ("Haight-Ashbury", "Russian Hill"): 17,
        ("Haight-Ashbury", "Marina District"): 17,
        ("Haight-Ashbury", "Financial District"): 21,
        ("Haight-Ashbury", "Alamo Square"): 5,
        ("Haight-Ashbury", "Golden Gate Park"): 7,
        ("Haight-Ashbury", "The Castro"): 6,
        ("Haight-Ashbury", "Bayview"): 18,
        ("Haight-Ashbury", "Sunset District"): 15,
        ("Haight-Ashbury", "Nob Hill"): 15,
        ("Nob Hill", "Russian Hill"): 5,
        ("Nob Hill", "Marina District"): 11,
        ("Nob Hill", "Financial District"): 9,
        ("Nob Hill", "Alamo Square"): 11,
        ("Nob Hill", "Golden Gate Park"): 17,
        ("Nob Hill", "The Castro"): 17,
        ("Nob Hill", "Bayview"): 19,
        ("Nob Hill", "Sunset District"): 24,
        ("Nob Hill", "Haight-Ashbury"): 13
    }

    # Convert times to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(h, m):
        return h * 60 + m

    def minutes_to_time(m):
        h = m // 60
        m = m % 60
        return f"{h:02d}:{m:02d}"

    # Create Z3 variables for each meeting's start and end times
    meeting_vars = {}
    for name in friends:
        start_var = Int(f"start_{name}")
        end_var = Int(f"end_{name}")
        meeting_vars[name] = {"start": start_var, "end": end_var}

    # Variables to track whether a meeting is scheduled
    scheduled = {name: Bool(f"scheduled_{name}") for name in friends}

    # Current location starts at Russian Hill at 9:00 AM (540 minutes)
    current_location = "Russian Hill"
    current_time = 540  # 9:00 AM in minutes

    # Constraints for each meeting
    for name in friends:
        friend = friends[name]
        start_min = time_to_minutes(*friend["start"])
        end_min = time_to_minutes(*friend["end"])
        min_duration = friend["min_duration"]

        # If scheduled, must meet duration and time window constraints
        s.add(Implies(scheduled[name], And(
            meeting_vars[name]["start"] >= start_min,
            meeting_vars[name]["end"] <= end_min,
            meeting_vars[name]["end"] - meeting_vars[name]["start"] >= min_duration
        )))

    # Create a list to represent the order of meetings
    meeting_order = [name for name in friends]
    
    # For each pair of meetings, ensure they don't overlap considering travel time
    for i in range(len(meeting_order)):
        for j in range(i+1, len(meeting_order)):
            name1 = meeting_order[i]
            name2 = meeting_order[j]
            
            # Travel time between locations
            travel_time1 = travel_times.get(
                (friends[name1]["location"], friends[name2]["location"]), 0)
            travel_time2 = travel_times.get(
                (friends[name2]["location"], friends[name1]["location"]), 0)
            
            # Either name1 is before name2 (with travel time) or vice versa
            s.add(Implies(And(scheduled[name1], scheduled[name2]),
                Or(
                    meeting_vars[name2]["start"] >= meeting_vars[name1]["end"] + travel_time1,
                    meeting_vars[name1]["start"] >= meeting_vars[name2]["end"] + travel_time2
                ))

    # Maximize the number of scheduled meetings
    s.maximize(Sum([If(scheduled[name], 1, 0) for name in friends]))

    # Check if the schedule is feasible
    if s.check() == sat:
        model = s.model()
        itinerary = []
        scheduled_meetings = []
        for name in friends:
            if is_true(model[scheduled[name]]):
                start = model[meeting_vars[name]["start"]].as_long()
                end = model[meeting_vars[name]["end"]].as_long()
                scheduled_meetings.append((start, name))

        # Sort meetings by start time
        scheduled_meetings.sort()
        for start, name in scheduled_meetings:
            end = model[meeting_vars[name]["end"]].as_long()
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": minutes_to_time(start),
                "end_time": minutes_to_time(end)
            })
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the problem and print the solution
solution = solve_scheduling_problem()
print(json.dumps(solution, indent=2))