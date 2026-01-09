from constraint import Problem

def main():
    problem = Problem()
    
    # Define work hours (9:00 to 17:00) in 30-minute intervals
    work_start = 9 * 2  # 9:00 as 18 half-hours from midnight
    work_end = 17 * 2   # 17:00 as 34 half-hours from midnight
    
    # Create list of possible time slots
    time_slots = list(range(work_start, work_end))
    
    # Add variable for meeting start time (in half-hour units from midnight)
    problem.addVariable('start_time', time_slots)
    
    # Define constraints for each person's busy times
    # Raymond's busy slots (convert times to half-hour units)
    raymond_busy = [
        (9*2, 9*2 + 1),   # 9:00-9:30
        (11*2 + 1, 12*2), # 11:30-12:00  
        (13*2, 13*2 + 1), # 13:00-13:30
        (15*2, 15*2 + 1)  # 15:00-15:30
    ]
    
    # Billy's busy slots
    billy_busy = [
        (10*2, 10*2 + 1),   # 10:00-10:30
        (12*2, 13*2),       # 12:00-13:00
        (16*2 + 1, 17*2)    # 16:30-17:00
    ]
    
    # Donald's busy slots  
    donald_busy = [
        (9*2, 9*2 + 1),     # 9:00-9:30
        (10*2, 11*2),       # 10:00-11:00
        (12*2, 13*2),       # 12:00-13:00
        (14*2, 14*2 + 1),   # 14:00-14:30
        (16*2, 17*2)        # 16:00-17:00
    ]
    
    # Define constraint function
    def time_constraint(start):
        # Meeting duration is 30 minutes (1 time slot)
        end = start + 1
        
        # Check if meeting fits within work hours
        if end > work_end:
            return False
            
        # Check Raymond's availability
        for busy_start, busy_end in raymond_busy:
            if not (end <= busy_start or start >= busy_end):
                return False
                
        # Check Billy's availability
        for busy_start, busy_end in billy_busy:
            if not (end <= busy_start or start >= busy_end):
                return False
                
        # Check Donald's availability  
        for busy_start, busy_end in donald_busy:
            if not (end <= busy_start or start >= busy_end):
                return False
                
        # Billy's preference: avoid meetings after 15:00
        if start >= 15 * 2:  # 15:00 or later
            return False
            
        return True
    
    problem.addConstraint(time_constraint, ['start_time'])
    
    # Find solution
    solutions = problem.getSolutions()
    
    if solutions:
        solution = solutions[0]
        start_slot = solution['start_time']
        
        # Convert back to time format
        start_hour = start_slot // 2
        start_minute = (start_slot % 2) * 30
        
        end_slot = start_slot + 1
        end_hour = end_slot // 2
        end_minute = (end_slot % 2) * 30
        
        # Format output
        time_range = f"{start_hour:02d}:{start_minute:02d}-{end_hour:02d}:{end_minute:02d}"
        print(f"Monday {time_range}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()