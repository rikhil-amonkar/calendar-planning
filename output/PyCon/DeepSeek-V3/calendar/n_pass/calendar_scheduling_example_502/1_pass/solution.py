from constraint import Problem

def main():
    problem = Problem()
    
    # Define work hours (9:00 to 17:00)
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 30  # minutes
    
    # Convert busy times to minutes since midnight
    jack_busy = [
        (9*60 + 30, 10*60 + 30),   # 9:30-10:30
        (11*60, 11*60 + 30),       # 11:00-11:30
        (12*60 + 30, 13*60),       # 12:30-13:00
        (14*60, 14*60 + 30),       # 14:00-14:30
        (16*60, 16*60 + 30)        # 16:00-16:30
    ]
    
    charlotte_busy = [
        (9*60 + 30, 10*60),        # 9:30-10:00
        (10*60 + 30, 12*60),       # 10:30-12:00
        (12*60 + 30, 13*60 + 30),  # 12:30-13:30
        (14*60, 16*60)             # 14:00-16:00
    ]
    
    # Define possible start times (every 15 minutes for efficiency)
    possible_starts = list(range(work_start, work_end - meeting_duration + 1, 15))
    
    # Add variable for meeting start time
    problem.addVariable('start_time', possible_starts)
    
    # Constraint: Meeting must end before work ends
    def ends_before_work_end(start):
        return start + meeting_duration <= work_end
    problem.addConstraint(ends_before_work_end, ['start_time'])
    
    # Constraint: Meeting must not overlap with Jack's busy times
    def jack_available(start):
        end = start + meeting_duration
        for busy_start, busy_end in jack_busy:
            if not (end <= busy_start or start >= busy_end):
                return False
        return True
    problem.addConstraint(jack_available, ['start_time'])
    
    # Constraint: Meeting must not overlap with Charlotte's busy times
    def charlotte_available(start):
        end = start + meeting_duration
        for busy_start, busy_end in charlotte_busy:
            if not (end <= busy_start or start >= busy_end):
                return False
        return True
    problem.addConstraint(charlotte_available, ['start_time'])
    
    # Constraint: Jack prefers no meetings after 12:30
    def jack_preference(start):
        return start + meeting_duration <= 12 * 60 + 30
    problem.addConstraint(jack_preference, ['start_time'])
    
    # Find solution
    solutions = problem.getSolutions()
    
    if solutions:
        solution = solutions[0]
        start_minutes = solution['start_time']
        end_minutes = start_minutes + meeting_duration
        
        # Convert to HH:MM format
        start_hour = start_minutes // 60
        start_minute = start_minutes % 60
        end_hour = end_minutes // 60
        end_minute = end_minutes % 60
        
        print(f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}")
        print("Monday")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()