from constraint import Problem

def main():
    problem = Problem()
    
    # Define work hours (9:00 to 17:00)
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 30
    
    # Convert all times to minutes since midnight for easier calculation
    # Megan's busy times
    megan_busy = [
        (9*60, 9*60+30),   # 9:00-9:30
        (10*60, 11*60),    # 10:00-11:00
        (12*60, 12*60+30)  # 12:00-12:30
    ]
    
    # Christine's busy times
    christine_busy = [
        (9*60, 9*60+30),     # 9:00-9:30
        (11*60+30, 12*60),   # 11:30-12:00
        (13*60, 14*60),      # 13:00-14:00
        (15*60+30, 16*60+30) # 15:30-16:30
    ]
    
    # Gabriel is free all day
    gabriel_busy = []
    
    # Sara's busy times
    sara_busy = [
        (11*60+30, 12*60),   # 11:30-12:00
        (14*60+30, 15*60)    # 14:30-15:00
    ]
    
    # Bruce's busy times
    bruce_busy = [
        (9*60+30, 10*60),    # 9:30-10:00
        (10*60+30, 12*60),   # 10:30-12:00
        (12*60+30, 14*60),   # 12:30-14:00
        (14*60+30, 15*60),   # 14:30-15:00
        (15*60+30, 16*60+30) # 15:30-16:30
    ]
    
    # Kathryn's busy times
    kathryn_busy = [
        (10*60, 15*60+30),   # 10:00-15:30
        (16*60, 16*60+30)    # 16:00-16:30
    ]
    
    # Billy's busy times
    billy_busy = [
        (9*60, 9*60+30),     # 9:00-9:30
        (11*60, 11*60+30),   # 11:00-11:30
        (12*60, 14*60),      # 12:00-14:00
        (14*60+30, 15*60+30) # 14:30-15:30
    ]
    
    # All participants' busy times
    all_busy = [megan_busy, christine_busy, gabriel_busy, sara_busy, 
                bruce_busy, kathryn_busy, billy_busy]
    
    # Define possible start times (every 15 minutes for efficiency)
    possible_starts = list(range(work_start, work_end - meeting_duration + 1, 15))
    
    # Add variable for meeting start time
    problem.addVariable('start_time', possible_starts)
    
    # Define constraint: meeting should not overlap with any participant's busy time
    def no_overlap(start_time):
        end_time = start_time + meeting_duration
        
        for participant_busy in all_busy:
            for busy_start, busy_end in participant_busy:
                # Check if meeting overlaps with this busy period
                if not (end_time <= busy_start or start_time >= busy_end):
                    return False
        return True
    
    problem.addConstraint(no_overlap, ['start_time'])
    
    # Find solutions
    solutions = problem.getSolutions()
    
    if solutions:
        # Take the first solution
        start_time_minutes = solutions[0]['start_time']
        end_time_minutes = start_time_minutes + meeting_duration
        
        # Convert back to HH:MM format
        start_hour = start_time_minutes // 60
        start_minute = start_time_minutes % 60
        end_hour = end_time_minutes // 60
        end_minute = end_time_minutes % 60
        
        # Format the output
        time_range = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
        print(f"Monday:{time_range}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()