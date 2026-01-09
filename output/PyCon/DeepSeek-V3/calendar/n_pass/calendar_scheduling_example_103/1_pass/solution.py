from constraint import Problem

def main():
    problem = Problem()
    
    # Define work hours (9:00 to 17:00)
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 30  # minutes
    
    # Convert blocked times to minutes since midnight
    diane_blocked = [(9*60+30, 10*60), (14*60+30, 15*60)]
    jack_blocked = [(13*60+30, 14*60), (14*60+30, 15*60)]
    eugene_blocked = [(9*60, 10*60), (10*60+30, 11*60+30), (12*60, 14*60+30), (15*60, 16*60+30)]
    patricia_blocked = [(9*60+30, 10*60+30), (11*60, 12*60), (12*60+30, 14*60), (15*60, 16*60+30)]
    
    # Define possible start times (every minute within work hours)
    possible_starts = list(range(work_start, work_end - meeting_duration + 1))
    
    problem.addVariable("start_time", possible_starts)
    
    # Constraint: meeting must not overlap with any blocked time for any participant
    def no_overlap(start):
        end = start + meeting_duration
        
        # Check Diane's schedule
        for block_start, block_end in diane_blocked:
            if start < block_end and end > block_start:
                return False
        
        # Check Jack's schedule
        for block_start, block_end in jack_blocked:
            if start < block_end and end > block_start:
                return False
        
        # Check Eugene's schedule
        for block_start, block_end in eugene_blocked:
            if start < block_end and end > block_start:
                return False
        
        # Check Patricia's schedule
        for block_start, block_end in patricia_blocked:
            if start < block_end and end > block_start:
                return False
        
        return True
    
    problem.addConstraint(no_overlap, ["start_time"])
    
    # Find a solution
    solutions = problem.getSolutions()
    
    if solutions:
        solution = solutions[0]
        start_minutes = solution["start_time"]
        end_minutes = start_minutes + meeting_duration
        
        # Convert minutes to HH:MM format
        start_hour = start_minutes // 60
        start_minute = start_minutes % 60
        end_hour = end_minutes // 60
        end_minute = end_minutes % 60
        
        print(f"Monday:{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()