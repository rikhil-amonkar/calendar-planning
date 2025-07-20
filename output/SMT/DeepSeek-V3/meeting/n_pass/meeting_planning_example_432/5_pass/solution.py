from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 solver
    s = Solver()

    # Define the meetings and their constraints
    meetings = [
        {"person": "Joseph", "location": "Fisherman's Wharf", "available_start": "8:00", "available_end": "17:30", "duration": 90},
        {"person": "Jeffrey", "location": "Bayview", "available_start": "17:30", "available_end": "21:30", "duration": 60},
        {"person": "Kevin", "location": "Mission District", "available_start": "11:15", "available_end": "15:15", "duration": 30},
        {"person": "David", "location": "Embarcadero", "available_start": "8:15", "available_end": "9:00", "duration": 30},
        {"person": "Barbara", "location": "Financial District", "available_start": "10:30", "available_end": "16:30", "duration": 15}
    ]

    # Convert time strings to minutes since midnight
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Location options and travel times
    locations = ["Golden Gate Park", "Fisherman's Wharf", "Bayview", 
                "Mission District", "Embarcadero", "Financial District"]
    travel_matrix = [
        [0, 24, 23, 17, 25, 26],    # Golden Gate Park
        [25, 0, 26, 22, 8, 11],      # Fisherman's Wharf
        [22, 25, 0, 13, 19, 19],     # Bayview
        [17, 22, 15, 0, 19, 17],     # Mission District
        [25, 6, 21, 20, 0, 5],       # Embarcadero
        [23, 10, 19, 17, 4, 0]       # Financial District
    ]

    # Current location starts at Golden Gate Park at 9:00 AM (540 minutes)
    current_loc_idx = 0  # Golden Gate Park
    current_time = 540

    # Create variables for each meeting
    meeting_vars = []
    for meeting in meetings:
        start = Int(f"start_{meeting['person']}")
        end = Int(f"end_{meeting['person']}")
        meeting_vars.append((meeting, start, end))

    # Constraints for each meeting
    for meeting, start, end in meeting_vars:
        available_start = time_to_minutes(meeting["available_start"])
        available_end = time_to_minutes(meeting["available_end"])
        s.add(start >= available_start)
        s.add(end <= available_end)
        s.add(end == start + meeting["duration"])

    # Create variables to track the schedule
    scheduled = [Bool(f"scheduled_{i}") for i in range(len(meeting_vars))]
    path_loc = [Int(f"path_loc_{i}") for i in range(len(meeting_vars) + 1)]
    path_time = [Int(f"path_time_{i}") for i in range(len(meeting_vars) + 1)]

    # Initial constraints
    s.add(path_loc[0] == current_loc_idx)
    s.add(path_time[0] == current_time)

    # Add travel time constraints
    for i in range(len(meeting_vars)):
        meeting, start, end = meeting_vars[i]
        meeting_loc_idx = locations.index(meeting["location"])
        
        # If meeting is scheduled
        s.add(Implies(scheduled[i],
            And(
                start >= path_time[i] + travel_matrix[path_loc[i]][meeting_loc_idx],
                path_loc[i+1] == meeting_loc_idx,
                path_time[i+1] == end
            )))
        
        # If meeting is not scheduled
        s.add(Implies(Not(scheduled[i]),
            And(
                path_loc[i+1] == path_loc[i],
                path_time[i+1] == path_time[i]
            )))

    # Try to maximize the number of scheduled meetings
    s.maximize(Sum([If(scheduled[i], 1, 0) for i in range(len(meeting_vars))]))

    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(len(meeting_vars)):
            if is_true(model.evaluate(scheduled[i])):
                meeting, start, end = meeting_vars[i]
                start_val = model.evaluate(start).as_long()
                end_val = model.evaluate(end).as_long()
                itinerary.append({
                    "action": "meet",
                    "person": meeting["person"],
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