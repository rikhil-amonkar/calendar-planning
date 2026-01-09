from constraint import Problem

def main():
    problem = Problem()
    
    # Define days and time slots in minutes from 9:00 (540 minutes) to 17:00 (1020 minutes)
    days = ['Monday', 'Tuesday', 'Wednesday']
    start_min = 540  # 9:00 in minutes
    end_min = 1020   # 17:00 in minutes
    meeting_duration = 60  # 1 hour in minutes
    
    # Add variables: day and start time
    problem.addVariable('day', days)
    problem.addVariable('start_time', range(start_min, end_min - meeting_duration + 1))
    
    # Martha's busy times in minutes from start of day
    martha_busy = [
        # Monday: 16:00-17:00 (960-1020)
        ('Monday', 960, 1020),
        # Tuesday: 15:00-15:30 (900-930)
        ('Tuesday', 900, 930),
        # Wednesday: 10:00-11:00 (600-660), 14:00-14:30 (840-870)
        ('Wednesday', 600, 660),
        ('Wednesday', 840, 870)
    ]
    
    # Beverly's busy times in minutes from start of day
    beverly_busy = [
        # Monday: 9:00-13:30 (540-810), 14:00-17:00 (840-1020)
        ('Monday', 540, 810),
        ('Monday', 840, 1020),
        # Tuesday: 9:00-17:00 (540-1020)
        ('Tuesday', 540, 1020),
        # Wednesday: 9:30-15:30 (570-930), 16:30-17:00 (990-1020)
        ('Wednesday', 570, 930),
        ('Wednesday', 990, 1020)
    ]
    
    def constraint(day, start_time):
        end_time = start_time + meeting_duration
        
        # Check Martha's schedule
        for busy_day, busy_start, busy_end in martha_busy:
            if busy_day == day:
                if not (end_time <= busy_start or start_time >= busy_end):
                    return False
        
        # Check Beverly's schedule
        for busy_day, busy_start, busy_end in beverly_busy:
            if busy_day == day:
                if not (end_time <= busy_start or start_time >= busy_end):
                    return False
        
        return True
    
    problem.addConstraint(constraint, ['day', 'start_time'])
    
    solutions = problem.getSolutions()
    
    if solutions:
        solution = solutions[0]
        day = solution['day']
        start_minutes = solution['start_time']
        end_minutes = start_minutes + meeting_duration
        
        # Convert minutes to HH:MM format
        start_hour = start_minutes // 60
        start_minute = start_minutes % 60
        end_hour = end_minutes // 60
        end_minute = end_minutes % 60
        
        print(f"{day}")
        print(f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()