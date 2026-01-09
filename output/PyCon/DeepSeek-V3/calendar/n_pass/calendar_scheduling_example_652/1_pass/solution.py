from constraint import Problem

def main():
    problem = Problem()
    
    # Define days
    days = ['Monday', 'Tuesday']
    
    # Define time slots in minutes from 9:00 (540 minutes) to 17:00 (1020 minutes)
    # Using 30-minute intervals
    start_minutes = list(range(540, 1020, 30))
    
    # Add variables - day and start time
    problem.addVariable('day', days)
    problem.addVariable('start_minute', start_minutes)
    
    # Define busy times for Jesse (in minutes from midnight)
    jesse_busy = []
    # Monday: 13:30-14:00 (810-840), 14:30-15:00 (870-900)
    jesse_busy.extend([(810, 840), (870, 900)])
    # Tuesday: 9:00-9:30 (540-570), 13:00-13:30 (780-810), 14:00-15:00 (840-900)
    jesse_busy.extend([(540, 570), (780, 810), (840, 900)])
    
    # Define busy times for Lawrence (in minutes from midnight)
    lawrence_busy = []
    # Monday: 9:00-17:00 (540-1020) - completely busy
    lawrence_busy.extend([(540, 1020)])
    # Tuesday: 9:30-10:30 (570-630), 11:30-12:30 (690-750), 13:00-13:30 (780-810), 
    # 14:30-15:00 (870-900), 15:30-16:30 (930-990)
    lawrence_busy.extend([(570, 630), (690, 750), (780, 810), (870, 900), (930, 990)])
    
    # Lawrence cannot meet on Tuesday after 16:30 (990 minutes)
    
    def time_conflict(day, start_minute):
        duration = 30
        end_minute = start_minute + duration
        
        # Check if meeting fits within work hours
        if start_minute < 540 or end_minute > 1020:
            return False
        
        # Check Lawrence's Tuesday after 16:30 constraint
        if day == 'Tuesday' and start_minute >= 990:
            return False
        
        # Check Jesse's schedule
        for busy_start, busy_end in jesse_busy:
            if day == 'Monday' and busy_start >= 810:  # Jesse's Monday meetings
                if not (end_minute <= busy_start or start_minute >= busy_end):
                    return False
            elif day == 'Tuesday' and busy_start >= 540:  # Jesse's Tuesday meetings
                if not (end_minute <= busy_start or start_minute >= busy_end):
                    return False
        
        # Check Lawrence's schedule
        for busy_start, busy_end in lawrence_busy:
            if day == 'Monday' and busy_start == 540:  # Lawrence's Monday (completely busy)
                return False
            elif day == 'Tuesday' and busy_start >= 570:  # Lawrence's Tuesday meetings
                if not (end_minute <= busy_start or start_minute >= busy_end):
                    return False
        
        return True
    
    problem.addConstraint(time_conflict, ['day', 'start_minute'])
    
    solutions = problem.getSolutions()
    
    if solutions:
        solution = solutions[0]
        day = solution['day']
        start_minute = solution['start_minute']
        end_minute = start_minute + 30
        
        # Convert minutes to HH:MM format
        start_hour = start_minute // 60
        start_min = start_minute % 60
        end_hour = end_minute // 60
        end_min = end_minute % 60
        
        print(f"{day}: {start_hour:02d}:{start_min:02d}-{end_hour:02d}:{end_min:02d}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()