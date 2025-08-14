from z3 import *

# Define the locations
locations = ["Embarcadero", "Richmond District", "Union Square", "Financial District", "Pacific Heights", "Nob Hill", "Bayview"]

# Define the travel times between locations (in minutes)
travel_times = {
    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "Union Square"): 10,
    ("Embarcadero", "Financial District"): 5,
    ("Embarcadero", "Pacific Heights"): 11,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "Bayview"): 21,
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "Union Square"): 21,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "Pacific Heights"): 10,
    ("Richmond District", "Nob Hill"): 17,
    ("Richmond District", "Bayview"): 26,
    ("Union Square", "Embarcadero"): 11,
    ("Union Square", "Richmond District"): 20,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Bayview"): 15,
    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "Union Square"): 9,
    ("Financial District", "Pacific Heights"): 13,
    ("Financial District", "Nob Hill"): 8,
    ("Financial District", "Bayview"): 19,
    ("Pacific Heights", "Embarcadero"): 10,
    ("Pacific Heights", "Richmond District"): 12,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Financial District"): 13,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Bayview"): 22,
    ("Nob Hill", "Embarcadero"): 9,
    ("Nob Hill", "Richmond District"): 14,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "Financial District"): 9,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "Bayview"): 19,
    ("Bayview", "Embarcadero"): 19,
    ("Bayview", "Richmond District"): 25,
    ("Bayview", "Union Square"): 17,
    ("Bayview", "Financial District"): 19,
    ("Bayview", "Pacific Heights"): 23,
    ("Bayview", "Nob Hill"): 20,
}

# Define the friends and their availability
friends = {
    "Kenneth": {"location": "Richmond District", "start": 915, "end": 1000, "duration": 30},
    "Lisa": {"location": "Union Square", "start": 900, "end": 1630, "duration": 45},
    "Joshua": {"location": "Financial District", "start": 1200, "end": 1515, "duration": 15},
    "Nancy": {"location": "Pacific Heights", "start": 800, "end": 1130, "duration": 90},
    "Andrew": {"location": "Nob Hill", "start": 1130, "end": 2015, "duration": 60},
    "John": {"location": "Bayview", "start": 1645, "end": 2130, "duration": 75},
}

# Convert time to minutes since start of the day (9:00 AM)
def time_to_minutes(time_str):
    hours, minutes = divmod(time_str, 100)
    return (hours - 9) * 60 + minutes

# Function to check if a given number of meetings is feasible
def check_feasibility(num_meetings):
    # Create a solver instance
    solver = Solver()

    # Define variables
    arrival_times = {friend: Int(f"arrival_{friend}") for friend in friends}
    meeting_times = {friend: Int(f"meeting_{friend}") for friend in friends}
    met_friends = {friend: Bool(f"met_{friend}") for friend in friends}

    # Add constraints for each friend
    for friend, details in friends.items():
        loc = details["location"]
        start = time_to_minutes(details["start"])
        end = time_to_minutes(details["end"])
        duration = details["duration"]
        
        # Meeting must start after arrival and before the friend leaves
        solver.add(Implies(met_friends[friend], arrival_times[friend] + duration <= meeting_times[friend]))
        solver.add(Implies(met_friends[friend], meeting_times[friend] <= end))
        
        # Meeting must start after the friend arrives
        solver.add(Implies(met_friends[friend], start <= meeting_times[friend] - duration))
        
        # Travel time constraints
        if friend != "Nancy":  # Nancy is the first meeting, starting at Embarcadero at 9:00 AM
            prev_loc = "Embarcadero"
            prev_meeting_time = 0
            for f, d in friends.items():
                if f == friend:
                    break
                prev_loc = d["location"]
                prev_meeting_time = meeting_times[f]
            travel_time = travel_times[(prev_loc, loc)]
            solver.add(Implies(met_friends[friend], prev_meeting_time + travel_time <= arrival_times[friend]))

    # Ensure exactly num_meetings friends are met
    solver.add(Sum([If(met_friends[friend], 1, 0) for friend in friends]) == num_meetings)

    # Check if the problem is solvable
    if solver.check() == sat:
        model = solver.model()
        solution = {friend: model.evaluate(meeting_times[friend]) for friend in friends if model.evaluate(met_friends[friend])}
        return True, solution
    else:
        return False, {}

# Iterate to find a feasible solution with exactly 6 meetings
for num_meetings in range(6, 0, -1):
    feasible, solution = check_feasibility(num_meetings)
    if feasible:
        print("SOLUTION:")
        for friend, meeting_time in solution.items():
            print(f"{friend}: Meeting at {meeting_time} minutes past 9:00 AM")
        break
else:
    print("No solution found that meets exactly 6 people")