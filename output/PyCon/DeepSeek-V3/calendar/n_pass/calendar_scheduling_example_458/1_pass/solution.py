from constraint import Problem

def main():
    problem = Problem()
    
    # Define work hours (9:00 to 17:00)
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 30  # minutes
    
    # Convert all schedules to minutes since midnight
    # Melissa: 10:00-11:00, 12:30-14:00, 15:00-15:30
    melissa_busy = [(10*60, 11*60), (12*60+30, 14*60), (15*60, 15*60+30)]
    
    # Gregory: 12:30-13:00, 15:30-16:00
    gregory_busy = [(12*60+30, 13*60), (15*60+30, 16*60)]
    
    # Victoria: 9:00-9:30, 10:30-11:30, 13:00-14:00, 14:30-15:00, 15:30-16:30
    victoria_busy = [(9*60, 9*60+30), (10*60+30, 11*60+30), (13*60, 14*60), 
                     (14*60+30, 15*60), (15*60+30, 16*60+30)]
    
    # Thomas: 10:00-12:00, 12:30-13:00, 14:30-16:00
    thomas_busy = [(10*60, 12*60), (12*60+30, 13*60), (14*60+30, 16*60)]
    
    # Jennifer: 9:00-9:30, 10:00-10:30, 11:00-13:00, 13:30-14:30, 15:00-15:30, 16:00-16:30
    jennifer_busy = [(9*60, 9*60+30), (10*60, 10*60+30), (11*60, 13*60), 
                     (13*60+30, 14*60+30), (15*60, 15*60+30), (16*60, 16*60+30)]
    
    # Wayne wants to avoid meetings before 14:00
    wayne_preference = 14 * 60
    
    # Define possible start times (every 15 minutes for efficiency)
    possible_starts = list(range(work_start, work_end - meeting_duration + 1, 15))
    
    problem.addVariable("start_time", possible_starts)
    
    def is_valid_time(start_time):
        end_time = start_time + meeting_duration
        
        # Check if meeting fits within work hours
        if end_time > work_end:
            return False
            
        # Wayne's preference: avoid before 14:00
        if start_time < wayne_preference:
            return False
            
        # Check Melissa's availability
        for busy_start, busy_end in melissa_busy:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
                
        # Check Gregory's availability
        for busy_start, busy_end in gregory_busy:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
                
        # Check Victoria's availability
        for busy_start, busy_end in victoria_busy:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
                
        # Check Thomas's availability
        for busy_start, busy_end in thomas_busy:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
                
        # Check Jennifer's availability
        for busy_start, busy_end in jennifer_busy:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
                
        return True
    
    problem.addConstraint(is_valid_time, ["start_time"])
    
    solutions = problem.getSolutions()
    
    if solutions:
        # Get the first solution
        start_time_minutes = solutions[0]["start_time"]
        end_time_minutes = start_time_minutes + meeting_duration
        
        # Convert back to HH:MM format
        start_hour = start_time_minutes // 60
        start_minute = start_time_minutes % 60
        end_hour = end_time_minutes // 60
        end_minute = end_time_minutes % 60
        
        print(f"Monday: {start_hour:02d}:{start_minute:02d}-{end_hour:02d}:{end_minute:02d}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()