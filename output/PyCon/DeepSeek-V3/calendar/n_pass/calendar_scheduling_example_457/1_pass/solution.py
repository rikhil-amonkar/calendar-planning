from constraint import Problem

def main():
    # Create problem instance
    problem = Problem()
    
    # Define work hours (9:00 to 17:00)
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    
    # Meeting duration in minutes
    meeting_duration = 30
    
    # Convert all schedules to minutes since midnight
    # Andrea: 9:30-10:30, 13:30-14:30
    andrea_busy = [(9*60+30, 10*60+30), (13*60+30, 14*60+30)]
    
    # Ruth: 12:30-13:00, 15:00-15:30
    ruth_busy = [(12*60+30, 13*60+0), (15*60+0, 15*60+30)]
    
    # Steven: 10:00-10:30, 11:00-11:30, 12:00-12:30, 13:30-14:00, 15:00-16:00
    steven_busy = [(10*60+0, 10*60+30), (11*60+0, 11*60+30), 
                   (12*60+0, 12*60+30), (13*60+30, 14*60+0),
                   (15*60+0, 16*60+0)]
    
    # Grace: no meetings
    grace_busy = []
    
    # Kyle: 9:00-9:30, 10:30-12:00, 12:30-13:00, 13:30-15:00, 15:30-16:00, 16:30-17:00
    kyle_busy = [(9*60+0, 9*60+30), (10*60+30, 12*60+0),
                 (12*60+30, 13*60+0), (13*60+30, 15*60+0),
                 (15*60+30, 16*60+0), (16*60+30, 17*60+0)]
    
    # Elijah: 9:00-11:00, 11:30-13:00, 13:30-14:00, 15:30-16:00, 16:30-17:00
    elijah_busy = [(9*60+0, 11*60+0), (11*60+30, 13*60+0),
                   (13*60+30, 14*60+0), (15*60+30, 16*60+0),
                   (16*60+30, 17*60+0)]
    
    # Lori: 9:00-9:30, 10:00-11:30, 12:00-13:30, 14:00-16:00, 16:30-17:00
    lori_busy = [(9*60+0, 9*60+30), (10*60+0, 11*60+30),
                 (12*60+0, 13*60+30), (14*60+0, 16*60+0),
                 (16*60+30, 17*60+0)]
    
    # Combine all schedules
    all_schedules = [andrea_busy, ruth_busy, steven_busy, grace_busy, 
                     kyle_busy, elijah_busy, lori_busy]
    
    # Define variable for meeting start time (in minutes from midnight)
    problem.addVariable("start_time", range(work_start, work_end - meeting_duration + 1))
    
    # Add constraint: meeting should not overlap with anyone's busy times
    def no_overlap(start_time):
        end_time = start_time + meeting_duration
        
        for schedule in all_schedules:
            for busy_start, busy_end in schedule:
                # Check if meeting overlaps with this busy period
                if not (end_time <= busy_start or start_time >= busy_end):
                    return False
        return True
    
    problem.addConstraint(no_overlap, ["start_time"])
    
    # Find solution
    solutions = problem.getSolutions()
    
    if solutions:
        # Get the first solution
        start_time_minutes = solutions[0]["start_time"]
        
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