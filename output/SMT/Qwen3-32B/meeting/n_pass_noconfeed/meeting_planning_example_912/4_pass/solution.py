import z3
import json

# Sample data: list of friends with their details
friends = {
    "Alice": {
        "location": "Coffee Shop",
        "available_times": [9*60, 10*60],  # [start, end] in minutes
        "min_duration": 30
    },
    "Bob": {
        "location": "Park",
        "available_times": [10*60, 12*60],
        "min_duration": 45
    },
    "Charlie": {
        "location": "Library",
        "available_times": [11*60, 13*60],
        "min_duration": 20
    }
}

# Create Z3 variables for each friend
start_times = {name: z3.Int(f"start_{name}") for name in friends}
visited = {name: z3.Bool(f"visited_{name}") for name in friends}

# Initialize the solver
solver = z3.Solver()

# Add constraints
for name in friends:
    # If visited, start time must be within available time window
    solver.add(z3.Implies(visited[name], z3.And(
        start_times[name] >= friends[name]["available_times"][0],
        start_times[name] <= friends[name]["available_times"][1] - friends[name]["min_duration"]
    )))

    # Ensure start times are non-negative
    solver.add(start_times[name] >= 0)

# Optional: add more constraints like only one meeting per hour, etc.

# Check for solution
if solver.check() == z3.sat:
    model = solver.model()
    visited_names = [name for name in friends if model.eval(visited[name])]
    visited_meetings = []
    for name in visited_names:
        start_val = model.eval(start_times[name]).as_long()
        duration = friends[name]['min_duration']
        end_val = start_val + duration
        visited_meetings.append({
            'name': name,
            'start': start_val,
            'end': end_val
        })
    visited_meetings.sort(key=lambda x: x['start'])

    def to_time_str(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours}:{mins:02d}"

    itinerary = []
    for item in visited_meetings:
        itinerary.append({
            "action": "meet",
            "location": friends[item['name']]['location'],
            "person": item['name'],
            "start_time": to_time_str(item['start']),
            "end_time": to_time_str(item['end'])
        })
    print(json.dumps({"itinerary": itinerary}))
else:
    print("No solution found.")