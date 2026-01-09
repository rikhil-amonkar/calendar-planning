from constraint import Problem

def main():
    problem = Problem()
    
    # Define work hours (9:00 to 17:00)
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    
    # Meeting duration in minutes
    meeting_duration = 30
    
    # Convert all schedules to minutes since midnight
    # Patrick
    patrick_busy = [
        (13*60 + 30, 14*60),
        (14*60 + 30, 15*60)
    ]
    
    # Shirley
    shirley_busy = [
        (9*60, 9*60 + 30),
        (11*60, 11*60 + 30),
        (12*60, 12*60 + 30),
        (14*60 + 30, 15*60),
        (16*60, 17*60)
    ]
    
    # Jeffrey
    jeffrey_busy = [
        (9*60, 9*60 + 30),
        (10*60 + 30, 11*60),
        (11*60 + 30, 12*60),
        (13*60, 13*60 + 30),
        (16*60, 17*60)
    ]
    
    # Gloria
    gloria_busy = [
        (11*60 + 30, 12*60),
        (15*60, 15*60 + 30)
    ]
    
    # Nathan
    nathan_busy = [
        (9*60, 9*60 + 30),
        (10*60 + 30, 12*60),
        (14*60, 17*60)
    ]
    
    # Angela
    angela_busy = [
        (9*60, 9*60 + 30),
        (10*60, 11*60),
        (12*60 + 30, 15*60),
        (15*60 + 30, 16*60 + 30)
    ]
    
    # David
    david_busy = [
        (9*60, 9*60 + 30),
        (10*60, 10*60 + 30),
        (11*60, 14*60),
        (14*60 + 30, 16*60 + 30)
    ]
    
    # All schedules in one list
    all_schedules = [
        patrick_busy, shirley_busy, jeffrey_busy, gloria_busy,
        nathan_busy, angela_busy, david_busy
    ]
    
    # Define variable for meeting start time (in minutes)
    problem.addVariable('start_time', range(work_start, work_end - meeting_duration + 1))
    
    # Add constraint that meeting should not overlap with anyone's busy times
    def no_overlap(start_time, schedules):
        meeting_end = start_time + meeting_duration
        
        for person_schedule in schedules:
            person_available = True
            for busy_start, busy_end in person_schedule:
                # Check if meeting overlaps with any busy period
                if not (meeting_end <= busy_start or start_time >= busy_end):
                    person_available = False
                    break
            
            # If this person is not available, the time doesn't work
            if not person_available:
                return False
        
        return True
    
    problem.addConstraint(no_overlap, ['start_time'])
    
    # Get solutions
    solutions = problem.getSolutions()
    
    if solutions:
        # Take the first solution
        start_time_minutes = solutions[0]['start_time']
        
        # Convert back to time format
        start_hour = start_time_minutes // 60
        start_minute = start_time_minutes % 60
        
        end_time_minutes = start_time_minutes + meeting_duration
        end_hour = end_time_minutes // 60
        end_minute = end_time_minutes % 60
        
        # Format output
        time_range = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
        day = "Monday"
        
        print(f"{time_range}")
        print(f"{day}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()