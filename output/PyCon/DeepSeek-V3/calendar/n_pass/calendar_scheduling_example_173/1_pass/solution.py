from constraint import Problem

def main():
    problem = Problem()
    
    # Define work hours (9:00 to 17:00)
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 30
    
    # Convert all times to minutes since midnight
    # Jacqueline's busy times
    jacqueline_busy = [
        (9*60, 9*60+30),   # 9:00-9:30
        (11*60, 11*60+30), # 11:00-11:30
        (12*60+30, 13*60), # 12:30-13:00
        (15*60+30, 16*60)  # 15:30-16:00
    ]
    
    # Harold's busy times
    harold_busy = [
        (10*60, 10*60+30), # 10:00-10:30
        (13*60, 13*60+30), # 13:00-13:30
        (15*60, 17*60)     # 15:00-17:00
    ]
    
    # Arthur's busy times
    arthur_busy = [
        (9*60, 9*60+30),   # 9:00-9:30
        (10*60, 12*60+30), # 10:00-12:30
        (14*60+30, 15*60), # 14:30-15:00
        (15*60+30, 17*60)  # 15:30-17:00
    ]
    
    # Kelly's busy times
    kelly_busy = [
        (9*60, 9*60+30),   # 9:00-9:30
        (10*60, 11*60),    # 10:00-11:00
        (11*60+30, 12*60+30), # 11:30-12:30
        (14*60, 15*60),    # 14:00-15:00
        (15*60+30, 16*60)  # 15:30-16:00
    ]
    
    # Define possible start times (every 30 minutes within work hours)
    possible_start_times = list(range(work_start, work_end - meeting_duration + 1, 30))
    
    # Add variable for meeting start time
    problem.addVariable("meeting_start", possible_start_times)
    
    # Constraint: Meeting must not overlap with anyone's busy times
    def no_overlap(start_time, busy_slots):
        meeting_end = start_time + meeting_duration
        for busy_start, busy_end in busy_slots:
            if not (meeting_end <= busy_start or start_time >= busy_end):
                return False
        return True
    
    problem.addConstraint(lambda start: no_overlap(start, jacqueline_busy), ["meeting_start"])
    problem.addConstraint(lambda start: no_overlap(start, harold_busy), ["meeting_start"])
    problem.addConstraint(lambda start: no_overlap(start, arthur_busy), ["meeting_start"])
    problem.addConstraint(lambda start: no_overlap(start, kelly_busy), ["meeting_start"])
    
    # Harold's preference: don't want to meet after 13:00
    problem.addConstraint(lambda start: start + meeting_duration <= 13*60, ["meeting_start"])
    
    # Find solution
    solutions = problem.getSolutions()
    
    if solutions:
        meeting_start = solutions[0]["meeting_start"]
        meeting_end = meeting_start + meeting_duration
        
        # Convert back to HH:MM format
        start_hour = meeting_start // 60
        start_minute = meeting_start % 60
        end_hour = meeting_end // 60
        end_minute = meeting_end % 60
        
        print(f"Monday:{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()