from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 optimizer
    opt = Optimize()

    # Define friends and their details
    friends = [
        {"name": "Mark", "location": "Marina District", "available_start": "18:45", "available_end": "21:00", "min_duration": 90},
        {"name": "Karen", "location": "Financial District", "available_start": "09:30", "available_end": "12:45", "min_duration": 90},
        {"name": "Barbara", "location": "Alamo Square", "available_start": "10:00", "available_end": "19:30", "min_duration": 90},
        {"name": "Nancy", "location": "Golden Gate Park", "available_start": "16:45", "available_end": "20:00", "min_duration": 105},
        {"name": "David", "location": "The Castro", "available_start": "09:00", "available_end": "18:00", "min_duration": 120},
        {"name": "Linda", "location": "Bayview", "available_start": "18:15", "available_end": "19:45", "min_duration": 45},
        {"name": "Kevin", "location": "Sunset District", "available_start": "10:00", "available_end": "17:45", "min_duration": 120},
        {"name": "Matthew", "location": "Haight-Ashbury", "available_start": "10:15", "available_end": "15:30", "min_duration": 45},
        {"name": "Andrew", "location": "Nob Hill", "available_start": "11:45", "available_end": "16:45", "min_duration": 105}
    ]

    # Travel times dictionary (simplified for this example)
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

    # Convert time strings to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Create variables for each friend's meeting start and end times
    meeting_vars = {}
    for friend in friends:
        name = friend["name"]
        available_start = time_to_minutes(friend["available_start"])
        available_end = time_to_minutes(friend["available_end"])
        min_duration = friend["min_duration"]

        # Start and end times as Z3 variables
        start = Int(f"start_{name}")
        end = Int(f"end_{name}")

        # Add constraints for meeting within availability and duration
        opt.add(start >= available_start)
        opt.add(end <= available_end)
        opt.add(end - start >= min_duration)

        meeting_vars[name] = {"start": start, "end": end, "location": friend["location"]}

    # Add constraints for travel times between consecutive meetings
    # We need to define the order of meetings to ensure travel times are respected
    # For simplicity, let's assume we can meet all friends in some order
    # and ensure that the end time of one meeting plus travel time is <= start time of the next

    # Define a variable for the order of meetings
    order = [Int(f"order_{i}") for i in range(len(friends))]
    # Each order variable must be between 0 and len(friends)-1
    for o in order:
        opt.add(o >= 0)
        opt.add(o < len(friends))
    # All order variables must be distinct
    opt.add(Distinct(order))

    # Define start and end times for each meeting based on order
    for i in range(len(friends)):
        for j in range(i + 1, len(friends)):
            # Get the friends at positions i and j in the order
            f1 = friends[order[i]]
            f2 = friends[order[j]]
            # Ensure that the end time of f1 plus travel time is <= start time of f2
            opt.add(meeting_vars[f1["name"]]["end"] + travel_times.get((f1["location"], f2["location"]), 0) <= meeting_vars[f2["name"]]["start"])

    # Maximize the number of friends met
    opt.maximize(Sum([If(meeting_vars[f["name"]]["end"] - meeting_vars[f["name"]]["start"] >= f["min_duration"], 1, 0) for f in friends]))

    # Check if a solution exists
    if opt.check() == sat:
        m = opt.model()
        itinerary = []
        for friend in friends:
            name = friend["name"]
            start_val = m[meeting_vars[name]["start"]].as_long()
            end_val = m[meeting_vars[name]["end"]].as_long()
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": minutes_to_time(start_val),
                "end_time": minutes_to_time(end_val)
            })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: time_to_minutes(x["start_time"]))
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the problem and print the solution
solution = solve_scheduling_problem()
print("SOLUTION:")
print(json.dumps(solution, indent=2))