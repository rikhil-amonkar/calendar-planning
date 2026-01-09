from constraint import Problem

def main():
    # Create problem instance
    problem = Problem()
    
    # Define work hours (9:00 to 17:00)
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 30  # minutes
    
    # Convert schedules to minutes from midnight
    # Eric: no meetings (free all day)
    eric_busy = []
    
    # Ashley: 10:00-10:30, 11:00-12:00, 12:30-13:00, 15:00-16:00
    ashley_busy = [
        (10 * 60, 10 * 60 + 30),
        (11 * 60, 12 * 60),
        (12 * 60 + 30, 13 * 60),
        (15 * 60, 16 * 60)
    ]
    
    # Ronald: 9:00-9:30, 10:00-11:30, 12:30-14:00, 14:30-17:00
    ronald_busy = [
        (9 * 60, 9 * 60 + 30),
        (10 * 60, 11 * 60 + 30),
        (12 * 60 + 30, 14 * 60),
        (14 * 60 + 30, 17 * 60)
    ]
    
    # Larry: 9:00-12:00, 13:00-17:00
    larry_busy = [
        (9 * 60, 12 * 60),
        (13 * 60, 17 * 60)
    ]
    
    # Define possible start times (every minute within work hours)
    possible_starts = list(range(work_start, work_end - meeting_duration + 1))
    
    # Add variable for meeting start time
    problem.addVariable('start_time', possible_starts)
    
    # Define constraint function
    def is_time_available(start_time, busy_slots):
        end_time = start_time + meeting_duration
        for busy_start, busy_end in busy_slots:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
        return True
    
    # Add constraints for each participant
    problem.addConstraint(lambda start: is_time_available(start, eric_busy), ['start_time'])
    problem.addConstraint(lambda start: is_time_available(start, ashley_busy), ['start_time'])
    problem.addConstraint(lambda start: is_time_available(start, ronald_busy), ['start_time'])
    problem.addConstraint(lambda start: is_time_available(start, larry_busy), ['start_time'])
    
    # Find solution
    solutions = problem.getSolutions()
    
    if solutions:
        # Get the first solution
        start_time_minutes = solutions[0]['start_time']
        end_time_minutes = start_time_minutes + meeting_duration
        
        # Convert to HH:MM format
        start_hour = start_time_minutes // 60
        start_minute = start_time_minutes % 60
        end_hour = end_time_minutes // 60
        end_minute = end_time_minutes % 60
        
        # Format output
        start_str = f"{start_hour:02d}:{start_minute:02d}"
        end_str = f"{end_hour:02d}:{end_minute:02d}"
        
        print(f"Monday:{start_str}:{end_str}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()