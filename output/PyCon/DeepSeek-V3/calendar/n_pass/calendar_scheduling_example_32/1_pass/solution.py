from constraint import Problem

def main():
    problem = Problem()
    
    # Define work hours (9:00 to 17:00)
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 30  # minutes
    
    # Convert schedules to minutes since midnight
    emily_busy = [
        (10*60, 10*60+30),    # 10:00-10:30
        (11*60+30, 12*60+30), # 11:30-12:30
        (14*60, 15*60),       # 14:00-15:00
        (16*60, 16*60+30)     # 16:00-16:30
    ]
    
    melissa_busy = [
        (9*60+30, 10*60),     # 9:30-10:00
        (14*60+30, 15*60)     # 14:30-15:00
    ]
    
    frank_busy = [
        (10*60, 10*60+30),    # 10:00-10:30
        (11*60, 11*60+30),    # 11:00-11:30
        (12*60+30, 13*60),    # 12:30-13:00
        (13*60+30, 14*60+30), # 13:30-14:30
        (15*60, 16*60),       # 15:00-16:00
        (16*60+30, 17*60)     # 16:30-17:00
    ]
    
    # Frank doesn't want to meet after 9:30 (so only at exactly 9:00)
    frank_preference_end = 9 * 60 + 30
    
    # Possible start times (in minutes from midnight)
    possible_starts = list(range(work_start, work_end - meeting_duration + 1, 15))
    
    problem.addVariable("start_time", possible_starts)
    
    def is_available(start, busy_slots, duration):
        end = start + duration
        for busy_start, busy_end in busy_slots:
            if not (end <= busy_start or start >= busy_end):
                return False
        return True
    
    def constraint_emily(start):
        return is_available(start, emily_busy, meeting_duration)
    
    def constraint_melissa(start):
        return is_available(start, melissa_busy, meeting_duration)
    
    def constraint_frank(start):
        # Check if within Frank's preference (before or at 9:30)
        if start + meeting_duration > frank_preference_end:
            return False
        return is_available(start, frank_busy, meeting_duration)
    
    problem.addConstraint(constraint_emily, ["start_time"])
    problem.addConstraint(constraint_melissa, ["start_time"])
    problem.addConstraint(constraint_frank, ["start_time"])
    
    solutions = problem.getSolutions()
    
    if solutions:
        solution = solutions[0]
        start_minutes = solution["start_time"]
        end_minutes = start_minutes + meeting_duration
        
        start_hour = start_minutes // 60
        start_minute = start_minutes % 60
        end_hour = end_minutes // 60
        end_minute = end_minutes % 60
        
        print(f"Monday {start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()