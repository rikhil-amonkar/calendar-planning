from constraint import Problem

def main():
    # Create problem instance
    problem = Problem()
    
    # Define work hours (9:00 to 17:00)
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 30  # minutes
    
    # Convert blocked times to minutes since midnight
    doris_blocks = [(9*60, 11*60), (13*60+30, 14*60), (16*60, 16*60+30)]
    theresa_blocks = [(10*60, 12*60)]
    christian_blocks = []  # No meetings
    terry_blocks = [(9*60+30, 10*60), (11*60+30, 12*60), (12*60+30, 13*60), 
                   (13*60+30, 14*60), (14*60+30, 15*60), (15*60+30, 17*60)]
    carolyn_blocks = [(9*60, 10*60+30), (11*60, 11*60+30), (12*60, 13*60), 
                     (13*60+30, 14*60+30), (15*60, 17*60)]
    kyle_blocks = [(9*60, 9*60+30), (11*60+30, 12*60), (12*60+30, 13*60), 
                  (14*60+30, 17*60)]
    
    # Define possible meeting start times (every 15 minutes for efficiency)
    possible_starts = list(range(work_start, work_end - meeting_duration + 1, 15))
    
    # Add variable for meeting start time
    problem.addVariable('meeting_start', possible_starts)
    
    # Define constraint function
    def is_time_available(meeting_start):
        meeting_end = meeting_start + meeting_duration
        
        # Check if meeting fits within work hours
        if meeting_end > work_end:
            return False
        
        # Check Doris's availability
        for block_start, block_end in doris_blocks:
            if not (meeting_end <= block_start or meeting_start >= block_end):
                return False
        
        # Check Theresa's availability
        for block_start, block_end in theresa_blocks:
            if not (meeting_end <= block_start or meeting_start >= block_end):
                return False
        
        # Check Christian's availability (always available)
        # No blocks to check
        
        # Check Terry's availability
        for block_start, block_end in terry_blocks:
            if not (meeting_end <= block_start or meeting_start >= block_end):
                return False
        
        # Check Carolyn's availability
        for block_start, block_end in carolyn_blocks:
            if not (meeting_end <= block_start or meeting_start >= block_end):
                return False
        
        # Check Kyle's availability
        for block_start, block_end in kyle_blocks:
            if not (meeting_end <= block_start or meeting_start >= block_end):
                return False
        
        return True
    
    # Add constraint
    problem.addConstraint(is_time_available, ['meeting_start'])
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if solutions:
        # Get the first solution
        meeting_start_minutes = solutions[0]['meeting_start']
        meeting_end_minutes = meeting_start_minutes + meeting_duration
        
        # Convert back to time format
        start_hour = meeting_start_minutes // 60
        start_minute = meeting_start_minutes % 60
        end_hour = meeting_end_minutes // 60
        end_minute = meeting_end_minutes % 60
        
        # Format output
        print(f"Monday {start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()