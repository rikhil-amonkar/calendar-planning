from constraint import Problem
import datetime

def main():
    # Define work hours and days
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']
    
    # Define meeting duration
    meeting_duration = 30  # minutes
    
    # Define James' busy times in minutes from start of day
    james_busy = {
        'Monday': [
            (9*60, 9*60+30),    # 9:00-9:30
            (10*60+30, 11*60),  # 10:30-11:00
            (12*60+30, 13*60),  # 12:30-13:00
            (14*60+30, 15*60+30),  # 14:30-15:30
            (16*60+30, 17*60)   # 16:30-17:00
        ],
        'Tuesday': [
            (9*60, 11*60),      # 9:00-11:00
            (11*60+30, 12*60),  # 11:30-12:00
            (12*60+30, 15*60+30),  # 12:30-15:30
            (16*60, 17*60)      # 16:00-17:00
        ],
        'Wednesday': [
            (10*60, 11*60),     # 10:00-11:00
            (12*60, 13*60),     # 12:00-13:00
            (13*60+30, 16*60)   # 13:30-16:00
        ],
        'Thursday': [
            (9*60+30, 11*60+30),  # 9:30-11:30
            (12*60, 12*60+30),   # 12:00-12:30
            (13*60, 13*60+30),   # 13:00-13:30
            (14*60, 14*60+30),   # 14:00-14:30
            (16*60+30, 17*60)    # 16:30-17:00
        ]
    }
    
    # Cheryl prefers not to meet on Wednesday or Thursday
    preferred_days = ['Monday', 'Tuesday']
    
    # Create problem
    problem = Problem()
    
    # Add variables
    problem.addVariable('day', days)
    problem.addVariable('start_time', range(work_start, work_end - meeting_duration + 1))
    
    # Define constraint function
    def time_available(day, start_time):
        end_time = start_time + meeting_duration
        
        # Check if within work hours
        if start_time < work_start or end_time > work_end:
            return False
        
        # Check Cheryl's preference (avoid Wednesday and Thursday if possible)
        if day in ['Wednesday', 'Thursday']:
            # Only allow these days if no other option exists
            pass  # We'll handle this preference in the solution selection
        
        # Check James' availability
        if day in james_busy:
            for busy_start, busy_end in james_busy[day]:
                # Check for overlap
                if not (end_time <= busy_start or start_time >= busy_end):
                    return False
        
        return True
    
    # Add constraint
    problem.addConstraint(time_available, ['day', 'start_time'])
    
    # Find all solutions
    solutions = problem.getSolutions()
    
    if not solutions:
        print("No available time slot found")
        return
    
    # Sort solutions by day preference and start time
    def solution_score(solution):
        day = solution['day']
        start_time = solution['start_time']
        
        # Prefer Monday/Tuesday over Wednesday/Thursday
        day_score = 0 if day in preferred_days else 2
        # Prefer earlier times
        time_score = start_time
        
        return (day_score, time_score)
    
    best_solution = min(solutions, key=solution_score)
    
    # Format output
    day = best_solution['day']
    start_minutes = best_solution['start_time']
    end_minutes = start_minutes + meeting_duration
    
    start_hour = start_minutes // 60
    start_minute = start_minutes % 60
    end_hour = end_minutes // 60
    end_minute = end_minutes % 60
    
    print(f"{day} {start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}")

if __name__ == "__main__":
    main()