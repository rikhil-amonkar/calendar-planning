from constraint import Problem
import re

def main():
    # Create problem instance
    problem = Problem()
    
    # Work hours: 9:00 to 17:00 (9:00-17:00)
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    
    # Meeting duration: 30 minutes
    meeting_duration = 30
    
    # Convert schedules to minutes since midnight
    # David's busy times
    david_busy = [
        (11*60 + 30, 12*60),      # 11:30-12:00
        (14*60 + 30, 15*60)       # 14:30-15:00
    ]
    
    # Douglas's busy times  
    douglas_busy = [
        (9*60 + 30, 10*60),       # 9:30-10:00
        (11*60 + 30, 12*60),      # 11:30-12:00
        (13*60, 13*60 + 30),      # 13:00-13:30
        (14*60 + 30, 15*60)       # 14:30-15:00
    ]
    
    # Ralph's busy times
    ralph_busy = [
        (9*60, 9*60 + 30),        # 9:00-9:30
        (10*60, 11*60),           # 10:00-11:00
        (11*60 + 30, 12*60 + 30), # 11:30-12:30
        (13*60 + 30, 15*60),      # 13:30-15:00
        (15*60 + 30, 16*60),      # 15:30-16:00
        (16*60 + 30, 17*60)       # 16:30-17:00
    ]
    
    # Jordan's busy times
    jordan_busy = [
        (9*60, 10*60),            # 9:00-10:00
        (12*60, 12*60 + 30),      # 12:00-12:30
        (13*60, 13*60 + 30),      # 13:00-13:30
        (14*60 + 30, 15*60),      # 14:30-15:00
        (15*60 + 30, 17*60)       # 15:30-17:00
    ]
    
    # Define possible start times (every 15 minutes for efficiency)
    possible_starts = list(range(work_start, work_end - meeting_duration + 1, 15))
    
    # Add variable for meeting start time
    problem.addVariable('start_time', possible_starts)
    
    # Define constraint function
    def time_works_for_all(start):
        end = start + meeting_duration
        
        # David's constraints
        for busy_start, busy_end in david_busy:
            if not (end <= busy_start or start >= busy_end):
                return False
        # David doesn't want to meet before 14:00
        if start < 14 * 60:
            return False
            
        # Douglas's constraints
        for busy_start, busy_end in douglas_busy:
            if not (end <= busy_start or start >= busy_end):
                return False
                
        # Ralph's constraints  
        for busy_start, busy_end in ralph_busy:
            if not (end <= busy_start or start >= busy_end):
                return False
                
        # Jordan's constraints
        for busy_start, busy_end in jordan_busy:
            if not (end <= busy_start or start >= busy_end):
                return False
                
        return True
    
    # Add constraint
    problem.addConstraint(time_works_for_all, ['start_time'])
    
    # Solve
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
        
        print(f"Monday {start_str}:{end_str}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()