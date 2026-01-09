from constraint import Problem

def main():
    problem = Problem()
    
    # Define work hours (9:00 to 17:00 in minutes from 9:00)
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 30  # minutes
    
    # Convert busy times to minutes from 9:00
    lisa_busy = [
        (9*60, 9*60 + 30),    # 9:00-9:30
        (10*60 + 30, 11*60),  # 10:30-11:00
        (14*60, 16*60)        # 14:00-16:00
    ]
    
    anthony_busy = [
        (9*60, 9*60 + 30),      # 9:00-9:30
        (11*60, 11*60 + 30),    # 11:00-11:30
        (12*60 + 30, 13*60 + 30),  # 12:30-13:30
        (14*60, 15*60),         # 14:00-15:00
        (15*60 + 30, 16*60),    # 15:30-16:00
        (16*60 + 30, 17*60)     # 16:30-17:00
    ]
    
    # Define variable for meeting start time (in minutes from 9:00)
    problem.addVariable("start_time", range(work_start, work_end - meeting_duration + 1))
    
    # Add constraints for Lisa's availability
    def lisa_available(start_time):
        end_time = start_time + meeting_duration
        for busy_start, busy_end in lisa_busy:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
        return True
    
    # Add constraints for Anthony's availability
    def anthony_available(start_time):
        end_time = start_time + meeting_duration
        for busy_start, busy_end in anthony_busy:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
        return True
    
    problem.addConstraint(lisa_available, ["start_time"])
    problem.addConstraint(anthony_available, ["start_time"])
    
    # Find the earliest solution
    solutions = problem.getSolutions()
    if solutions:
        # Sort by start time to get earliest
        sorted_solutions = sorted(solutions, key=lambda x: x['start_time'])
        earliest = sorted_solutions[0]
        start_minutes = earliest['start_time']
        end_minutes = start_minutes + meeting_duration
        
        # Convert back to HH:MM format
        start_hour = start_minutes // 60
        start_minute = start_minutes % 60
        end_hour = end_minutes // 60
        end_minute = end_minutes % 60
        
        print(f"Monday:{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}")
    else:
        print("No available time slot found")

if __name__ == "__main__":
    main()