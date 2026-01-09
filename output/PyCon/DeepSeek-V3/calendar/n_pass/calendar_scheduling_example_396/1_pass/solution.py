from constraint import Problem

def main():
    # Define the problem
    problem = Problem()
    
    # Work hours: 9:00 to 17:00 (convert to minutes for easier calculation)
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 30  # minutes
    
    # Define time slots in 30-minute intervals
    time_slots = []
    current_time = work_start
    while current_time + meeting_duration <= work_end:
        time_slots.append(current_time)
        current_time += 30
    
    # Add variable for meeting start time
    problem.addVariable('meeting_start', time_slots)
    
    # Define busy times for each person (in minutes from midnight)
    # Andrea: free all day
    andrea_busy = []
    
    # Jack: 9:00-9:30, 14:00-14:30
    jack_busy = [(9*60, 9*60+30), (14*60, 14*60+30)]
    
    # Madison: 9:30-10:30, 13:00-14:00, 15:00-15:30, 16:30-17:00
    madison_busy = [(9*60+30, 10*60+30), (13*60, 14*60), 
                    (15*60, 15*60+30), (16*60+30, 17*60)]
    
    # Rachel: 9:30-10:30, 11:00-11:30, 12:00-13:30, 14:30-15:30, 16:00-17:00
    rachel_busy = [(9*60+30, 10*60+30), (11*60, 11*60+30), 
                   (12*60, 13*60+30), (14*60+30, 15*60+30), 
                   (16*60, 17*60)]
    
    # Douglas: 9:00-11:30, 12:00-16:30
    douglas_busy = [(9*60, 11*60+30), (12*60, 16*60+30)]
    
    # Ryan: 9:00-9:30, 13:00-14:00, 14:30-17:00
    ryan_busy = [(9*60, 9*60+30), (13*60, 14*60), (14*60+30, 17*60)]
    
    # Define constraint function
    def is_time_available(meeting_start):
        meeting_end = meeting_start + meeting_duration
        
        # Check if meeting conflicts with anyone's schedule
        for busy_start, busy_end in andrea_busy:
            if meeting_start < busy_end and meeting_end > busy_start:
                return False
        
        for busy_start, busy_end in jack_busy:
            if meeting_start < busy_end and meeting_end > busy_start:
                return False
                
        for busy_start, busy_end in madison_busy:
            if meeting_start < busy_end and meeting_end > busy_start:
                return False
                
        for busy_start, busy_end in rachel_busy:
            if meeting_start < busy_end and meeting_end > busy_start:
                return False
                
        for busy_start, busy_end in douglas_busy:
            if meeting_start < busy_end and meeting_end > busy_start:
                return False
                
        for busy_start, busy_end in ryan_busy:
            if meeting_start < busy_end and meeting_end > busy_start:
                return False
                
        return True
    
    # Add constraint
    problem.addConstraint(is_time_available, ['meeting_start'])
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if solutions:
        # Get the first solution
        meeting_start_minutes = solutions[0]['meeting_start']
        
        # Convert back to time format
        start_hour = meeting_start_minutes // 60
        start_minute = meeting_start_minutes % 60
        
        end_minutes = meeting_start_minutes + meeting_duration
        end_hour = end_minutes // 60
        end_minute = end_minutes % 60
        
        # Format the output
        start_time = f"{start_hour:02d}:{start_minute:02d}"
        end_time = f"{end_hour:02d}:{end_minute:02d}"
        
        print(f"Monday:{start_time}:{end_time}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()