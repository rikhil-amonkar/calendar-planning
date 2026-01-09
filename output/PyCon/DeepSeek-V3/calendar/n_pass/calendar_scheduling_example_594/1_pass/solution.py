from constraint import Problem

def main():
    # Create problem instance
    problem = Problem()
    
    # Define work hours (9:00 to 17:00)
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 30  # minutes
    
    # Convert busy times to minutes from midnight
    adam_busy = [
        (9 * 60 + 30, 10 * 60),      # 9:30-10:00
        (12 * 60 + 30, 13 * 60),     # 12:30-13:00
        (14 * 60 + 30, 15 * 60),     # 14:30-15:00
        (16 * 60 + 30, 17 * 60)      # 16:30-17:00
    ]
    
    roy_busy = [
        (10 * 60, 11 * 60),          # 10:00-11:00
        (11 * 60 + 30, 13 * 60),     # 11:30-13:00
        (13 * 60 + 30, 14 * 60 + 30), # 13:30-14:30
        (16 * 60 + 30, 17 * 60)      # 16:30-17:00
    ]
    
    # Define possible start times (every 15 minutes for efficiency)
    possible_starts = range(work_start, work_end - meeting_duration + 1, 15)
    
    # Add variable for meeting start time
    problem.addVariable('start_time', possible_starts)
    
    # Add constraint: meeting must fit within work hours
    def within_work_hours(start):
        return start >= work_start and start + meeting_duration <= work_end
    
    problem.addConstraint(within_work_hours, ['start_time'])
    
    # Add constraint: meeting must not overlap with Adam's busy times
    def not_overlap_adam(start):
        end = start + meeting_duration
        for busy_start, busy_end in adam_busy:
            if not (end <= busy_start or start >= busy_end):
                return False
        return True
    
    problem.addConstraint(not_overlap_adam, ['start_time'])
    
    # Add constraint: meeting must not overlap with Roy's busy times
    def not_overlap_roy(start):
        end = start + meeting_duration
        for busy_start, busy_end in roy_busy:
            if not (end <= busy_start or start >= busy_end):
                return False
        return True
    
    problem.addConstraint(not_overlap_roy, ['start_time'])
    
    # Find earliest solution
    solutions = problem.getSolutions()
    if not solutions:
        print("No available time slot found")
        return
    
    # Find earliest start time
    earliest_solution = min(solutions, key=lambda x: x['start_time'])
    start_minutes = earliest_solution['start_time']
    end_minutes = start_minutes + meeting_duration
    
    # Convert back to time format
    start_hour = start_minutes // 60
    start_minute = start_minutes % 60
    end_hour = end_minutes // 60
    end_minute = end_minutes % 60
    
    # Format output
    time_range = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
    print(f"{time_range}")
    print("Monday")

if __name__ == "__main__":
    main()