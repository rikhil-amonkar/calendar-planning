from constraint import Problem

def main():
    problem = Problem()
    
    # Define work hours (9:00 to 17:00)
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 30  # minutes
    
    # Convert schedules to minutes from midnight
    # Judy is free all day
    judy_busy = []
    
    # Nicole's busy times in minutes
    nicole_busy = [
        (9 * 60, 10 * 60),           # 9:00-10:00
        (10 * 60 + 30, 16 * 60 + 30) # 10:30-16:30
    ]
    
    # Nicole's preference: not before 16:00
    nicole_pref_start = 16 * 60
    
    # Define possible start times (in minutes from midnight)
    possible_start_times = []
    for start_minute in range(work_start, work_end - meeting_duration + 1):
        possible_start_times.append(start_minute)
    
    # Add variable for meeting start time
    problem.addVariable('meeting_start', possible_start_times)
    
    # Constraint: Meeting must not conflict with Judy's schedule
    def judy_available(meeting_start):
        meeting_end = meeting_start + meeting_duration
        for busy_start, busy_end in judy_busy:
            if not (meeting_end <= busy_start or meeting_start >= busy_end):
                return False
        return True
    
    # Constraint: Meeting must not conflict with Nicole's schedule
    def nicole_available(meeting_start):
        meeting_end = meeting_start + meeting_duration
        for busy_start, busy_end in nicole_busy:
            if not (meeting_end <= busy_start or meeting_start >= busy_end):
                return False
        return True
    
    # Constraint: Respect Nicole's preference (not before 16:00)
    def nicole_preference(meeting_start):
        return meeting_start >= nicole_pref_start
    
    problem.addConstraint(judy_available, ['meeting_start'])
    problem.addConstraint(nicole_available, ['meeting_start'])
    problem.addConstraint(nicole_preference, ['meeting_start'])
    
    # Find solutions
    solutions = problem.getSolutions()
    
    if solutions:
        # Take the first solution
        meeting_start_minutes = solutions[0]['meeting_start']
        meeting_end_minutes = meeting_start_minutes + meeting_duration
        
        # Convert back to HH:MM format
        start_hour = meeting_start_minutes // 60
        start_minute = meeting_start_minutes % 60
        end_hour = meeting_end_minutes // 60
        end_minute = meeting_end_minutes % 60
        
        # Format as HH:MM:HH:MM
        time_range = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
        
        print(f"Monday:{time_range}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()