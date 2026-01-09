# Add constraint for end time calculation
for friend in friends:
    name = friend["name"]
    min_duration = friend["min_duration"]
    
    def end_time_constraint(start, fd=friend):
        return start + fd["min_duration"]
    
    problem.addConstraint(end_time_constraint, [f"{name}_start", f"{name}_end"])