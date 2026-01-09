from constraint import Problem

def main():
    problem = Problem()
    
    # Define work hours (9:00 to 17:00) in minutes from start of day
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 60  # 1 hour in minutes
    
    # Convert all times to minutes from start of day for easier calculation
    # Ryan's busy periods
    ryan_busy = [
        (9 * 60, 9 * 60 + 30),    # 9:00-9:30
        (12 * 60 + 30, 13 * 60)   # 12:30-13:00
    ]
    
    # Ruth has no meetings
    ruth_busy = []
    
    # Denise's busy periods
    denise_busy = [
        (9 * 60 + 30, 10 * 60 + 30),  # 9:30-10:30
        (12 * 60, 13 * 60),           # 12:00-13:00
        (14 * 60 + 30, 16 * 60 + 30)  # 14:30-16:30
    ]
    
    # Denise doesn't want to meet after 12:30
    denise_no_meet_after = 12 * 60 + 30
    
    # Define possible start times (every 15 minutes for efficiency)
    possible_starts = range(work_start, work_end - meeting_duration + 1, 15)
    
    problem.addVariable("start_time", possible_starts)
    
    # Constraint: Meeting must end before work ends
    def work_hours_constraint(start):
        return start + meeting_duration <= work_end
    
    # Constraint: Meeting must not conflict with Ryan's schedule
    def ryan_available_constraint(start):
        end = start + meeting_duration
        for busy_start, busy_end in ryan_busy:
            if not (end <= busy_start or start >= busy_end):
                return False
        return True
    
    # Constraint: Meeting must not conflict with Ruth's schedule
    def ruth_available_constraint(start):
        end = start + meeting_duration
        for busy_start, busy_end in ruth_busy:
            if not (end <= busy_start or start >= busy_end):
                return False
        return True
    
    # Constraint: Meeting must not conflict with Denise's schedule
    def denise_available_constraint(start):
        end = start + meeting_duration
        for busy_start, busy_end in denise_busy:
            if not (end <= busy_start or start >= busy_end):
                return False
        return True
    
    # Constraint: Denise doesn't want to meet after 12:30
    def denise_time_preference_constraint(start):
        return start + meeting_duration <= denise_no_meet_after
    
    # Add all constraints
    problem.addConstraint(work_hours_constraint, ["start_time"])
    problem.addConstraint(ryan_available_constraint, ["start_time"])
    problem.addConstraint(ruth_available_constraint, ["start_time"])
    problem.addConstraint(denise_available_constraint, ["start_time"])
    problem.addConstraint(denise_time_preference_constraint, ["start_time"])
    
    # Find solutions
    solutions = problem.getSolutions()
    
    if solutions:
        # Get the first solution
        start_time_minutes = solutions[0]["start_time"]
        end_time_minutes = start_time_minutes + meeting_duration
        
        # Convert back to HH:MM format
        start_hour = start_time_minutes // 60
        start_minute = start_time_minutes % 60
        end_hour = end_time_minutes // 60
        end_minute = end_time_minutes % 60
        
        # Format the output
        time_range = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
        print(f"Monday:{time_range}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()