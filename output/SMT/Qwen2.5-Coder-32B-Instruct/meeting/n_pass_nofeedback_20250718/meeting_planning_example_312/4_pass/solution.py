from z3 import *

# Define the districts and their travel times
districts = ["Richmond District", "Sunset District", "Haight-Ashbury", "Mission District", "Golden Gate Park"]
travel_times = {
    ("Richmond District", "Sunset District"): 11,
    ("Richmond District", "Haight-Ashbury"): 10,
    ("Richmond District", "Mission District"): 20,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Sunset District", "Richmond District"): 12,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Sunset District", "Mission District"): 24,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Haight-Ashbury", "Richmond District"): 10,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Mission District", "Richmond District"): 20,
    ("Mission District", "Sunset District"): 24,
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Golden Gate Park"): 17,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Mission District"): 17,
}

# Define the friends and their availability
friends = {
    "Sarah": {"district": "Sunset District", "start": 10.75, "end": 19.00, "min_duration": 0.5},
    "Richard": {"district": "Haight-Ashbury", "start": 11.75, "end": 15.75, "min_duration": 1.5},
    "Elizabeth": {"district": "Mission District", "start": 11.00, "end": 17.25, "min_duration": 2.0},
    "Michelle": {"district": "Golden Gate Park", "start": 18.25, "end": 20.75, "min_duration": 1.5},
}

# Create a solver instance
solver = Solver()

# Define the variables
current_district = String("current_district")
current_time = Real("current_time")
meetings = {name: Bool(name) for name in friends}

# Initial conditions
solver.add(current_district == "Richmond District")
solver.add(current_time == 9.0)

# Define the constraints for each friend
for name, details in friends.items():
    district = details["district"]
    start = details["start"]
    end = details["end"]
    min_duration = details["min_duration"]
    
    # Define the meeting start and end times
    meeting_start = Real(f"{name}_start")
    meeting_end = Real(f"{name}_end")
    
    # Constraints for meeting with the friend
    solver.add(meeting_start >= start)
    solver.add(meeting_end <= end)
    solver.add(meeting_end - meeting_start >= min_duration)
    
    # Constraints for traveling to the friend's district
    travel_time = If(And(current_district == "Richmond District", district == "Sunset District"), 11/60.0,
                     If(And(current_district == "Richmond District", district == "Haight-Ashbury"), 10/60.0,
                        If(And(current_district == "Richmond District", district == "Mission District"), 20/60.0,
                           If(And(current_district == "Richmond District", district == "Golden Gate Park"), 9/60.0,
                              If(And(current_district == "Sunset District", district == "Richmond District"), 12/60.0,
                                 If(And(current_district == "Sunset District", district == "Haight-Ashbury"), 15/60.0,
                                    If(And(current_district == "Sunset District", district == "Mission District"), 24/60.0,
                                       If(And(current_district == "Sunset District", district == "Golden Gate Park"), 11/60.0,
                                          If(And(current_district == "Haight-Ashbury", district == "Richmond District"), 10/60.0,
                                             If(And(current_district == "Haight-Ashbury", district == "Sunset District"), 15/60.0,
                                                If(And(current_district == "Haight-Ashbury", district == "Mission District"), 11/60.0,
                                                   If(And(current_district == "Haight-Ashbury", district == "Golden Gate Park"), 7/60.0,
                                                      If(And(current_district == "Mission District", district == "Richmond District"), 20/60.0,
                                                         If(And(current_district == "Mission District", district == "Sunset District"), 24/60.0,
                                                            If(And(current_district == "Mission District", district == "Haight-Ashbury"), 12/60.0,
                                                               If(And(current_district == "Mission District", district == "Golden Gate Park"), 17/60.0,
                                                                  If(And(current_district == "Golden Gate Park", district == "Richmond District"), 7/60.0,
                                                                     If(And(current_district == "Golden Gate Park", district == "Sunset District"), 10/60.0,
                                                                        If(And(current_district == "Golden Gate Park", district == "Haight-Ashbury"), 7/60.0,
                                                                           If(And(current_district == "Golden Gate Park", district == "Mission District"), 17/60.0, 0)))))))))))))))))
    
    solver.add(meeting_start - current_time >= travel_time)
    
    # Constraints for traveling back to the next district
    next_district = String(f"{name}_next_district")
    next_time = Real(f"{name}_next_time")
    solver.add(next_time == meeting_end + travel_time)
    
    # Add the meeting to the solver
    solver.add(Implies(meetings[name], And(current_district == district, current_time == meeting_start, next_district == current_district, next_time == current_time)))
    solver.add(Implies(Not(meetings[name]), current_district == current_district))
    
    # Update the current district and time
    current_district = next_district
    current_time = next_time

# Maximize the number of meetings
solver.maximize(Sum([If(meetings[name], 1, 0) for name in friends]))

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for name, details in friends.items():
        if model.evaluate(meetings[name]):
            start = model.evaluate(Real(f"{name}_start")).as_decimal(2)
            end = model.evaluate(Real(f"{name}_end")).as_decimal(2)
            itinerary.append({"action": "meet", "person": name, "start_time": f"{int(start):02}:{int((start % 1) * 60):02}", "end_time": f"{int(end):02}:{int((end % 1) * 60):02}"})
    print({"itinerary": itinerary})
else:
    print("No solution found")