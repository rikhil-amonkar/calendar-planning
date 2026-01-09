from constraint import Problem

def main():
    problem = Problem()
    
    # Define work hours (9:00 to 17:00)
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 30  # minutes
    
    # Convert schedules to minutes from midnight
    eric_busy = [
        (12 * 60, 13 * 60),  # 12:00-13:00
        (14 * 60, 15 * 60)   # 14:00-15:00
    ]
    
    henry_busy = [
        (9 * 60 + 30, 10 * 60),      # 9:30-10:00
        (10 * 60 + 30, 11 * 60),     # 10:30-11:00
        (11 * 60 + 30, 12 * 60 + 30), # 11:30-12:30
        (13 * 60, 13 * 60 + 30),     # 13:00-13:30
        (14 * 60 + 30, 15 * 60),     # 14:30-15:00
        (16 * 60, 17 * 60)           # 16:00-17:00
    ]
    
    # Henry prefers not to meet after 10:00 (10:00 in minutes)
    henry_preference_cutoff = 10 * 60
    
    # Define possible start times (in minutes from midnight)
    start_times = range(work_start, work_end - meeting_duration + 1, 15)  # 15-minute intervals
    
    problem.addVariable("start_time", start_times)
    
    def is_valid_time(start_time):
        end_time = start_time + meeting_duration
        
        # Check if meeting fits within work hours
        if start_time < work_start or end_time > work_end:
            return False
            
        # Check Eric's availability
        for busy_start, busy_end in eric_busy:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
                
        # Check Henry's availability
        for busy_start, busy_end in henry_busy:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
                
        # Henry's preference: try to schedule before 10:00 if possible
        if start_time < henry_preference_cutoff:
            return True
        else:
            # Still valid but less preferred
            return True
            
        return False
    
    problem.addConstraint(is_valid_time, ["start_time"])
    
    # Find solutions
    solutions = problem.getSolutions()
    
    if solutions:
        # Sort solutions by preference (earlier times first, especially before 10:00)
        sorted_solutions = sorted(solutions, key=lambda x: (x["start_time"] >= henry_preference_cutoff, x["start_time"]))
        
        best_solution = sorted_solutions[0]
        start_minutes = best_solution["start_time"]
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