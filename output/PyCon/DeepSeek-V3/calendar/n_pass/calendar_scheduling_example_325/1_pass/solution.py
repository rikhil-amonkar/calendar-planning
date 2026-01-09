from constraint import Problem

def main():
    problem = Problem()
    
    # Define work hours (9:00 to 17:00)
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 30
    
    # Convert all schedules to minutes since midnight
    jose_busy = [(11*60, 11*60+30), (12*60+30, 13*60)]
    keith_busy = [(14*60, 14*60+30), (15*60, 15*60+30)]
    logan_busy = [(9*60, 10*60), (12*60, 12*60+30), (15*60, 15*60+30)]
    megan_busy = [(9*60, 10*60+30), (11*60, 12*60), (13*60, 13*60+30), (14*60+30, 16*60+30)]
    gary_busy = [(9*60, 9*60+30), (10*60, 10*60+30), (11*60+30, 13*60), (13*60+30, 14*60), (14*60+30, 16*60+30)]
    bobby_busy = [(11*60, 11*60+30), (12*60, 12*60+30), (13*60, 16*60)]
    
    # Jose doesn't want to meet after 15:30
    jose_pref_end = 15 * 60 + 30
    
    # Define possible start times (every minute within work hours)
    possible_starts = list(range(work_start, work_end - meeting_duration + 1))
    
    # Add variable for meeting start time
    problem.addVariable('start_time', possible_starts)
    
    # Define constraint function
    def is_available(start_time):
        end_time = start_time + meeting_duration
        
        # Check Jose's availability and preference
        if not all(end_time <= busy_start or start_time >= busy_end for busy_start, busy_end in jose_busy):
            return False
        if end_time > jose_pref_end:
            return False
            
        # Check Keith's availability
        if not all(end_time <= busy_start or start_time >= busy_end for busy_start, busy_end in keith_busy):
            return False
            
        # Check Logan's availability
        if not all(end_time <= busy_start or start_time >= busy_end for busy_start, busy_end in logan_busy):
            return False
            
        # Check Megan's availability
        if not all(end_time <= busy_start or start_time >= busy_end for busy_start, busy_end in megan_busy):
            return False
            
        # Check Gary's availability
        if not all(end_time <= busy_start or start_time >= busy_end for busy_start, busy_end in gary_busy):
            return False
            
        # Check Bobby's availability
        if not all(end_time <= busy_start or start_time >= busy_end for busy_start, busy_end in bobby_busy):
            return False
            
        return True
    
    problem.addConstraint(is_available, ['start_time'])
    
    # Find solution
    solutions = problem.getSolutions()
    
    if solutions:
        solution = solutions[0]
        start_minutes = solution['start_time']
        end_minutes = start_minutes + meeting_duration
        
        # Convert back to HH:MM format
        start_hour = start_minutes // 60
        start_minute = start_minutes % 60
        end_hour = end_minutes // 60
        end_minute = end_minutes % 60
        
        print(f"Monday:{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()