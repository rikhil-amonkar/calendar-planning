from constraint import Problem

def main():
    problem = Problem()
    
    # Define work hours (9:00 to 17:00)
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 60  # 1 hour in minutes
    
    # Convert busy times to minutes since midnight
    anthony_busy = [
        (9 * 60 + 30, 10 * 60),      # 9:30-10:00
        (12 * 60, 13 * 60),          # 12:00-13:00
        (16 * 60, 16 * 60 + 30)      # 16:00-16:30
    ]
    
    pamela_busy = [
        (9 * 60 + 30, 10 * 60),      # 9:30-10:00
        (16 * 60 + 30, 17 * 60)      # 16:30-17:00
    ]
    
    zachary_busy = [
        (9 * 60, 11 * 60 + 30),      # 9:00-11:30
        (12 * 60, 12 * 60 + 30),     # 12:00-12:30
        (13 * 60, 13 * 60 + 30),     # 13:00-13:30
        (14 * 60 + 30, 15 * 60),     # 14:30-15:00
        (16 * 60, 17 * 60)           # 16:00-17:00
    ]
    
    # Pamela's constraint: doesn't want to meet after 14:30
    pamela_max_time = 14 * 60 + 30
    
    # Define possible start times (in minutes from midnight)
    possible_starts = list(range(work_start, work_end - meeting_duration + 1, 15))
    
    problem.addVariable("start_time", possible_starts)
    
    # Constraint: meeting must end before work ends
    def work_hours_constraint(start):
        return start + meeting_duration <= work_end
    
    # Constraint: meeting must not conflict with Anthony's schedule
    def anthony_constraint(start):
        end = start + meeting_duration
        for busy_start, busy_end in anthony_busy:
            if not (end <= busy_start or start >= busy_end):
                return False
        return True
    
    # Constraint: meeting must not conflict with Pamela's schedule
    def pamela_constraint(start):
        end = start + meeting_duration
        for busy_start, busy_end in pamela_busy:
            if not (end <= busy_start or start >= busy_end):
                return False
        return True
    
    # Constraint: meeting must not conflict with Zachary's schedule
    def zachary_constraint(start):
        end = start + meeting_duration
        for busy_start, busy_end in zachary_busy:
            if not (end <= busy_start or start >= busy_end):
                return False
        return True
    
    # Constraint: Pamela doesn't want to meet after 14:30
    def pamela_time_constraint(start):
        return start + meeting_duration <= pamela_max_time
    
    problem.addConstraint(work_hours_constraint, ["start_time"])
    problem.addConstraint(anthony_constraint, ["start_time"])
    problem.addConstraint(pamela_constraint, ["start_time"])
    problem.addConstraint(zachary_constraint, ["start_time"])
    problem.addConstraint(pamela_time_constraint, ["start_time"])
    
    solutions = problem.getSolutions()
    
    if solutions:
        # Take the first solution
        start_minutes = solutions[0]["start_time"]
        end_minutes = start_minutes + meeting_duration
        
        # Convert to HH:MM format
        start_hour = start_minutes // 60
        start_minute = start_minutes % 60
        end_hour = end_minutes // 60
        end_minute = end_minutes % 60
        
        print(f"Monday {start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()