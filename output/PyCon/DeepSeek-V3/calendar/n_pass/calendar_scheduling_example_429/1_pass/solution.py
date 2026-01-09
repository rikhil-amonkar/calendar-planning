from constraint import Problem

def main():
    problem = Problem()
    
    # Define work hours (9:00 to 17:00)
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 30  # minutes
    
    # Convert all schedules to minutes since midnight
    # Judy: 13:00-13:30, 16:00-16:30
    judy_busy = [(13*60, 13*60+30), (16*60, 16*60+30)]
    
    # Olivia: 10:00-10:30, 12:00-13:00, 14:00-14:30
    olivia_busy = [(10*60, 10*60+30), (12*60, 13*60), (14*60, 14*60+30)]
    
    # Eric: free all day
    eric_busy = []
    
    # Jacqueline: 10:00-10:30, 15:00-15:30
    jacqueline_busy = [(10*60, 10*60+30), (15*60, 15*60+30)]
    
    # Laura: 9:00-10:00, 10:30-12:00, 13:00-13:30, 14:30-15:00, 15:30-17:00
    laura_busy = [(9*60, 10*60), (10*60+30, 12*60), (13*60, 13*60+30), 
                  (14*60+30, 15*60), (15*60+30, 17*60)]
    
    # Tyler: 9:00-10:00, 11:00-11:30, 12:30-13:00, 14:00-14:30, 15:30-17:00
    tyler_busy = [(9*60, 10*60), (11*60, 11*60+30), (12*60+30, 13*60), 
                  (14*60, 14*60+30), (15*60+30, 17*60)]
    
    # Lisa: 9:30-10:30, 11:00-11:30, 12:00-12:30, 13:00-13:30, 14:00-14:30, 16:00-17:00
    lisa_busy = [(9*60+30, 10*60+30), (11*60, 11*60+30), (12*60, 12*60+30), 
                 (13*60, 13*60+30), (14*60, 14*60+30), (16*60, 17*60)]
    
    # All busy periods combined
    all_busy = judy_busy + olivia_busy + eric_busy + jacqueline_busy + laura_busy + tyler_busy + lisa_busy
    
    # Define possible start times (every 15 minutes for efficiency)
    possible_starts = list(range(work_start, work_end - meeting_duration + 1, 15))
    
    problem.addVariable("start_time", possible_starts)
    
    def is_time_available(start_time):
        end_time = start_time + meeting_duration
        
        # Check if meeting fits within work hours
        if start_time < work_start or end_time > work_end:
            return False
            
        # Check if time conflicts with any busy period
        for busy_start, busy_end in all_busy:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
                
        return True
    
    problem.addConstraint(is_time_available, ["start_time"])
    
    solutions = problem.getSolutions()
    
    if solutions:
        # Take the first solution
        start_time_minutes = solutions[0]["start_time"]
        end_time_minutes = start_time_minutes + meeting_duration
        
        # Convert to HH:MM format
        start_hour = start_time_minutes // 60
        start_minute = start_time_minutes % 60
        end_hour = end_time_minutes // 60
        end_minute = end_time_minutes % 60
        
        print(f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}")
        print("Monday")
    else:
        print("No available time slot found")

if __name__ == "__main__":
    main()