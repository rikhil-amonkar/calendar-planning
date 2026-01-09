from constraint import Problem

def main():
    problem = Problem()
    
    # Define work hours (9:00 to 17:00)
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 30  # minutes
    
    # Convert all schedules to minutes since midnight
    # Gregory: 9:00-9:30, 11:30-12:00
    gregory_busy = [(9*60, 9*60+30), (11*60+30, 12*60)]
    
    # Jonathan: 9:00-9:30, 12:00-12:30, 13:00-13:30, 15:00-16:00, 16:30-17:00
    jonathan_busy = [(9*60, 9*60+30), (12*60, 12*60+30), (13*60, 13*60+30), 
                     (15*60, 16*60), (16*60+30, 17*60)]
    
    # Barbara: 10:00-10:30, 13:30-14:00
    barbara_busy = [(10*60, 10*60+30), (13*60+30, 14*60)]
    
    # Jesse: 10:00-11:00, 12:30-14:30
    jesse_busy = [(10*60, 11*60), (12*60+30, 14*60+30)]
    
    # Alan: 9:30-11:00, 11:30-12:30, 13:00-15:30, 16:00-17:00
    alan_busy = [(9*60+30, 11*60), (11*60+30, 12*60+30), 
                 (13*60, 15*60+30), (16*60, 17*60)]
    
    # Nicole: 9:00-10:30, 11:30-12:00, 12:30-13:30, 14:00-17:00
    nicole_busy = [(9*60, 10*60+30), (11*60+30, 12*60), 
                   (12*60+30, 13*60+30), (14*60, 17*60)]
    
    # Catherine: 9:00-10:30, 12:00-13:30, 15:00-15:30, 16:00-16:30
    catherine_busy = [(9*60, 10*60+30), (12*60, 13*60+30), 
                      (15*60, 15*60+30), (16*60, 16*60+30)]
    
    # All busy periods combined
    all_busy = gregory_busy + jonathan_busy + barbara_busy + jesse_busy + alan_busy + nicole_busy + catherine_busy
    
    # Define possible start times (every 15 minutes for efficiency)
    possible_starts = list(range(work_start, work_end - meeting_duration + 1, 15))
    
    problem.addVariable("start_time", possible_starts)
    
    # Constraint: meeting must not overlap with any busy period
    def no_overlap(start_time):
        meeting_end = start_time + meeting_duration
        
        for busy_start, busy_end in all_busy:
            if not (meeting_end <= busy_start or start_time >= busy_end):
                return False
        return True
    
    problem.addConstraint(no_overlap, ["start_time"])
    
    # Find solution
    solutions = problem.getSolutions()
    
    if solutions:
        solution = solutions[0]
        start_time_minutes = solution["start_time"]
        end_time_minutes = start_time_minutes + meeting_duration
        
        # Convert back to HH:MM format
        start_hour = start_time_minutes // 60
        start_minute = start_time_minutes % 60
        end_hour = end_time_minutes // 60
        end_minute = end_time_minutes % 60
        
        print(f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}")
        print("Monday")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()