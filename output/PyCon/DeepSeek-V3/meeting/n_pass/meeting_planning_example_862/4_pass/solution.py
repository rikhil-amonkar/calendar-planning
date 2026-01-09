# Add constraint for end time calculation
# Assuming 'friends' is defined elsewhere in your code
# If not, you'll need to define it first

# Example of how friends might be defined:
# friends = [
#     {"name": "Alice", "min_duration": 30},
#     {"name": "Bob", "min_duration": 45},
#     {"name": "Charlie", "min_duration": 60}
# ]

for friend in friends:
    name = friend["name"]
    min_duration = friend["min_duration"]
    
    # Create a closure to capture the current friend's min_duration
    def end_time_constraint(start, fd=friend):
        return start + fd["min_duration"]
    
    problem.addConstraint(end_time_constraint, [f"{name}_start", f"{name}_end"])