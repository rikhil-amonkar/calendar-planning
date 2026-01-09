# Define the friends list with their minimum durations
friends = [
    {"name": "Alice", "min_duration": 30},
    {"name": "Bob", "min_duration": 45},
    {"name": "Charlie", "min_duration": 60}
]

# Add constraint for end time calculation
for friend in friends:
    name = friend["name"]
    min_duration = friend["min_duration"]
    
    # Create a constraint function that ensures end = start + min_duration
    def end_time_constraint(start, end, fd=friend):
        return end == start + fd["min_duration"]
    
    problem.addConstraint(end_time_constraint, [f"{name}_start", f"{name}_end"])