from constraint import Problem

def main():
    # Define the problem
    problem = Problem()
    
    # Work hours
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 60  # 1 hour in minutes
    
    # Convert all times to minutes since midnight for easier calculation
    # Evelyn: free all day
    # Joshua: busy 11:00-12:30, 13:30-14:30, 16:30-17:00
    joshua_busy = [(11*60, 12*60+30), (13*60+30, 14*60+30), (16*60+30, 17*60)]
    # Kevin: free all day
    # Gerald: free all day
    # Jerry: busy 9:00-9:30, 10:30-12:00, 12:30-13:00, 13:30-14:00, 14:30-15:00, 15:30-16:00
    jerry_busy = [(9*60, 9*60+30), (10*60+30, 12*60), (12*60+30, 13*60), 
                  (13*60+30, 14*60), (14*60+30, 15*60), (15*60+30, 16*60)]
    # Jesse: busy 9:00-9:30, 10:30-12:00, 12:30-13:00, 14:30-15:00, 15:30-16:30
    jesse_busy = [(9*60, 9*60+30), (10*60+30, 12*60), (12*60+30, 13*60),
                  (14*60+30, 15*60), (15*60+30, 16*60+30)]
    # Kenneth: busy 10:30-12:30, 13:30-14:00, 14:30-15:00, 15:30-16:00, 16:30-17:00
    kenneth_busy = [(10*60+30, 12*60+30), (13*60+30, 14*60), (14*60+30, 15*60),
                    (15*60+30, 16*60), (16*60+30, 17*60)]
    
    # Define possible start times (every 30 minutes)
    possible_start_times = list(range(work_start, work_end - meeting_duration + 1, 30))
    
    # Add variable for meeting start time
    problem.addVariable('start_time', possible_start_times)
    
    # Define constraint function
    def is_time_available(start_time):
        end_time = start_time + meeting_duration
        
        # Check if meeting fits within work hours
        if start_time < work_start or end_time > work_end:
            return False
        
        # Check Joshua's availability
        for busy_start, busy_end in joshua_busy:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
        
        # Check Jerry's availability
        for busy_start, busy_end in jerry_busy:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
        
        # Check Jesse's availability
        for busy_start, busy_end in jesse_busy:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
        
        # Check Kenneth's availability
        for busy_start, busy_end in kenneth_busy:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
        
        return True
    
    # Add constraint
    problem.addConstraint(is_time_available, ['start_time'])
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if solutions:
        # Get the first solution (earliest time)
        start_time_minutes = solutions[0]['start_time']
        
        # Convert back to HH:MM format
        start_hour = start_time_minutes // 60
        start_minute = start_time_minutes % 60
        
        end_time_minutes = start_time_minutes + meeting_duration
        end_hour = end_time_minutes // 60
        end_minute = end_time_minutes % 60
        
        # Format the output
        start_time_str = f"{start_hour:02d}:{start_minute:02d}"
        end_time_str = f"{end_hour:02d}:{end_minute:02d}"
        
        print(f"Monday:{start_time_str}:{end_time_str}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()