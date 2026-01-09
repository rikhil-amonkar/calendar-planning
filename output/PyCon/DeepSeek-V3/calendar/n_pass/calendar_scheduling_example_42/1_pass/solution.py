from constraint import Problem

def main():
    # Create problem instance
    problem = Problem()
    
    # Define work hours (9:00 to 17:00 in 30-minute intervals)
    work_start = 9 * 2  # 9:00 as 18 half-hours from midnight
    work_end = 17 * 2   # 17:00 as 34 half-hours from midnight
    
    # Create time slots (each slot represents 30 minutes)
    time_slots = list(range(work_start, work_end))
    
    # Add variable for meeting start time (in 30-minute intervals from midnight)
    problem.addVariable('start_time', time_slots)
    
    # Define busy times for each person (in 30-minute intervals)
    # Julie: 9:00-9:30, 11:00-11:30, 12:00-12:30, 13:30-14:00, 16:00-17:00
    julie_busy = [18, 19, 22, 23, 24, 25, 27, 28, 32, 33, 34]
    
    # Sean: 9:00-9:30, 13:00-13:30, 15:00-15:30, 16:00-16:30
    sean_busy = [18, 19, 26, 27, 30, 31, 32, 33]
    
    # Lori: 10:00-10:30, 11:00-13:00, 15:30-17:00
    lori_busy = [20, 21, 22, 23, 24, 25, 26, 27, 31, 32, 33, 34]
    
    # Meeting duration: 1 hour = 2 time slots
    meeting_duration = 2
    
    def time_constraint(start):
        # Check if meeting fits within work hours
        if start + meeting_duration > work_end:
            return False
        
        # Check each time slot in the meeting duration
        for i in range(meeting_duration):
            current_slot = start + i
            
            # Check if any participant is busy during this slot
            if (current_slot in julie_busy or 
                current_slot in sean_busy or 
                current_slot in lori_busy):
                return False
        
        return True
    
    # Add constraint
    problem.addConstraint(time_constraint, ['start_time'])
    
    # Find solution
    solutions = problem.getSolutions()
    
    if solutions:
        # Get the first solution
        start_slot = solutions[0]['start_time']
        
        # Convert slot to time format
        start_hour = start_slot // 2
        start_minute = (start_slot % 2) * 30
        
        end_slot = start_slot + meeting_duration
        end_hour = end_slot // 2
        end_minute = (end_slot % 2) * 30
        
        # Format output
        start_time = f"{start_hour:02d}:{start_minute:02d}"
        end_time = f"{end_hour:02d}:{end_minute:02d}"
        
        print(f"Monday:{start_time}:{end_time}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()