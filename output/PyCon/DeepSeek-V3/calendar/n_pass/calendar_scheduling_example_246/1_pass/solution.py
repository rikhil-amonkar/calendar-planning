from constraint import Problem

def main():
    # Create problem instance
    problem = Problem()
    
    # Define work hours (9:00 to 17:00)
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 30  # minutes
    
    # Convert all times to minutes since midnight for easier calculation
    # Jacob's busy times
    jacob_busy = [
        (13*60 + 30, 14*60),      # 13:30-14:00
        (14*60 + 30, 15*60)       # 14:30-15:00
    ]
    
    # Diana's busy times
    diana_busy = [
        (9*60 + 30, 10*60),       # 9:30-10:00
        (11*60 + 30, 12*60),      # 11:30-12:00
        (13*60, 13*60 + 30),      # 13:00-13:30
        (16*60, 16*60 + 30)       # 16:00-16:30
    ]
    
    # Adam's busy times
    adam_busy = [
        (9*60 + 30, 10*60 + 30),  # 9:30-10:30
        (11*60, 12*60 + 30),      # 11:00-12:30
        (15*60 + 30, 16*60)       # 15:30-16:00
    ]
    
    # Angela's busy times
    angela_busy = [
        (9*60 + 30, 10*60),       # 9:30-10:00
        (10*60 + 30, 12*60),      # 10:30-12:00
        (13*60, 15*60 + 30),      # 13:00-15:30
        (16*60, 16*60 + 30)       # 16:00-16:30
    ]
    
    # Dennis's busy times
    dennis_busy = [
        (9*60, 9*60 + 30),        # 9:00-9:30
        (10*60 + 30, 11*60 + 30), # 10:30-11:30
        (13*60, 15*60),           # 13:00-15:00
        (16*60 + 30, 17*60)       # 16:30-17:00
    ]
    
    # Define possible start times (every 15 minutes for efficiency)
    possible_starts = list(range(work_start, work_end - meeting_duration + 1, 15))
    
    # Add variable for meeting start time
    problem.addVariable('start_time', possible_starts)
    
    # Define constraint function to check if time works for everyone
    def is_time_available(start_time):
        end_time = start_time + meeting_duration
        
        # Check Jacob's availability
        for busy_start, busy_end in jacob_busy:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
        
        # Check Diana's availability
        for busy_start, busy_end in diana_busy:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
        
        # Check Adam's availability
        for busy_start, busy_end in adam_busy:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
        
        # Check Angela's availability
        for busy_start, busy_end in angela_busy:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
        
        # Check Dennis's availability
        for busy_start, busy_end in dennis_busy:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
        
        return True
    
    # Add constraint
    problem.addConstraint(is_time_available, ['start_time'])
    
    # Find solution
    solutions = problem.getSolutions()
    
    if solutions:
        # Get the first solution
        solution = solutions[0]
        start_minutes = solution['start_time']
        end_minutes = start_minutes + meeting_duration
        
        # Convert back to time format
        start_hour = start_minutes // 60
        start_minute = start_minutes % 60
        end_hour = end_minutes // 60
        end_minute = end_minutes % 60
        
        # Format output
        print(f"Monday:{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()