from constraint import Problem

def main():
    problem = Problem()
    
    # Define work hours (9:00 to 17:00 in minutes from 9:00)
    work_start = 0  # 9:00 = 0 minutes
    work_end = 480  # 17:00 = 480 minutes (8 hours * 60)
    meeting_duration = 30
    
    # Convert schedules to minutes from 9:00
    # Kimberly: 10:00-10:30, 11:00-12:00, 16:00-16:30
    kimberly_busy = [(60, 90), (120, 180), (420, 450)]
    
    # Megan: no meetings, but prefers to avoid before 10:00
    megan_busy = []
    
    # Marie: 10:00-11:00, 11:30-15:00, 16:00-16:30
    marie_busy = [(60, 120), (150, 360), (420, 450)]
    
    # Diana: 9:30-10:00, 10:30-14:30, 15:30-17:00
    diana_busy = [(30, 60), (90, 330), (390, 480)]
    
    # Define possible start times (every 15 minutes for efficiency)
    possible_starts = list(range(work_start, work_end - meeting_duration + 1, 15))
    
    # Add variable for meeting start time
    problem.addVariable("start_time", possible_starts)
    
    # Define constraint function
    def time_works_for_all(start):
        end = start + meeting_duration
        
        # Check Kimberly
        for busy_start, busy_end in kimberly_busy:
            if not (end <= busy_start or start >= busy_end):
                return False
        
        # Check Megan (no meetings, but avoid before 10:00)
        if start < 60:  # 10:00 = 60 minutes from 9:00
            return False
        
        # Check Marie
        for busy_start, busy_end in marie_busy:
            if not (end <= busy_start or start >= busy_end):
                return False
        
        # Check Diana
        for busy_start, busy_end in diana_busy:
            if not (end <= busy_start or start >= busy_end):
                return False
        
        return True
    
    problem.addConstraint(time_works_for_all, ["start_time"])
    
    # Find solution
    solutions = problem.getSolutions()
    
    if solutions:
        solution = solutions[0]
        start_minutes = solution["start_time"]
        end_minutes = start_minutes + meeting_duration
        
        # Convert back to time format
        start_hour = 9 + start_minutes // 60
        start_minute = start_minutes % 60
        end_hour = 9 + end_minutes // 60
        end_minute = end_minutes % 60
        
        print(f"Monday:{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()