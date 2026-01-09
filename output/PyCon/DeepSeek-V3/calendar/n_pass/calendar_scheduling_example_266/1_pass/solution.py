from constraint import Problem

def main():
    problem = Problem()
    
    # Define work hours (9:00 to 17:00)
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 30  # minutes
    
    # Convert all schedules to minutes since midnight
    # Joe: 9:30-10:00, 10:30-11:00
    joe_busy = [(9*60+30, 10*60), (10*60+30, 11*60)]
    
    # Keith: 11:30-12:00, 15:00-15:30
    keith_busy = [(11*60+30, 12*60), (15*60, 15*60+30)]
    
    # Patricia: 9:00-9:30, 13:00-13:30
    patricia_busy = [(9*60, 9*60+30), (13*60, 13*60+30)]
    
    # Nancy: 9:00-11:00, 11:30-16:30
    nancy_busy = [(9*60, 11*60), (11*60+30, 16*60+30)]
    
    # Pamela: 9:00-10:00, 10:30-11:00, 11:30-12:30, 13:00-14:00, 14:30-15:00, 15:30-16:00, 16:30-17:00
    pamela_busy = [
        (9*60, 10*60), (10*60+30, 11*60), (11*60+30, 12*60+30),
        (13*60, 14*60), (14*60+30, 15*60), (15*60+30, 16*60),
        (16*60+30, 17*60)
    ]
    
    # Define possible start times (every 15 minutes for efficiency)
    possible_starts = list(range(work_start, work_end - meeting_duration + 1, 15))
    
    # Add variable for meeting start time
    problem.addVariable('meeting_start', possible_starts)
    
    # Define constraint function
    def is_time_available(start_time):
        end_time = start_time + meeting_duration
        
        # Check if time overlaps with any busy period for each person
        # Joe
        for busy_start, busy_end in joe_busy:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
        
        # Keith
        for busy_start, busy_end in keith_busy:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
        
        # Patricia
        for busy_start, busy_end in patricia_busy:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
        
        # Nancy
        for busy_start, busy_end in nancy_busy:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
        
        # Pamela
        for busy_start, busy_end in pamela_busy:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
        
        return True
    
    problem.addConstraint(is_time_available, ['meeting_start'])
    
    # Find solution
    solutions = problem.getSolutions()
    
    if solutions:
        # Get the first solution
        meeting_start_minutes = solutions[0]['meeting_start']
        meeting_end_minutes = meeting_start_minutes + meeting_duration
        
        # Convert to HH:MM format
        start_hour = meeting_start_minutes // 60
        start_minute = meeting_start_minutes % 60
        end_hour = meeting_end_minutes // 60
        end_minute = meeting_end_minutes % 60
        
        # Format output
        start_time_str = f"{start_hour:02d}:{start_minute:02d}"
        end_time_str = f"{end_hour:02d}:{end_minute:02d}"
        
        print(f"Monday:{start_time_str}:{end_time_str}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()