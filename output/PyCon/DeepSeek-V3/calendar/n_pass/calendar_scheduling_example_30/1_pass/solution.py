from constraint import Problem

def main():
    problem = Problem()
    
    # Define work hours (9:00 to 17:00 in 30-minute intervals)
    work_start = 9 * 2  # 9:00 as 18 half-hour units
    work_end = 17 * 2   # 17:00 as 34 half-hour units
    
    # Convert schedules to half-hour units from 9:00
    # Jeffrey: 9:30-10:00 (slots 1-2), 10:30-11:00 (slots 3-4)
    jeffrey_busy = [(1, 2), (3, 4)]
    
    # Virginia: 9:00-9:30 (slots 0-1), 10:00-10:30 (slots 2-3), 
    # 14:30-15:00 (slots 11-12), 16:00-16:30 (slots 14-15)
    virginia_busy = [(0, 1), (2, 3), (11, 12), (14, 15)]
    
    # Melissa: 9:00-11:30 (slots 0-5), 12:00-12:30 (slots 6-7),
    # 13:00-15:00 (slots 8-12), 16:00-17:00 (slots 14-16)
    melissa_busy = [(0, 5), (6, 7), (8, 12), (14, 16)]
    
    # Meeting duration: 30 minutes = 1 slot
    meeting_duration = 1
    
    # Define possible start times
    possible_starts = range(work_start, work_end - meeting_duration + 1)
    
    # Add variable for start time
    problem.addVariable('start', possible_starts)
    
    # Define constraint function
    def time_available(start):
        end = start + meeting_duration
        
        # Check Jeffrey's availability
        for busy_start, busy_end in jeffrey_busy:
            if not (end <= busy_start or start >= busy_end):
                return False
        
        # Check Virginia's availability
        for busy_start, busy_end in virginia_busy:
            if not (end <= busy_start or start >= busy_end):
                return False
        
        # Check Melissa's availability
        for busy_start, busy_end in melissa_busy:
            if not (end <= busy_start or start >= busy_end):
                return False
        
        # Melissa's preference: not after 14:00 (slot 10 = 14:00)
        if start >= 10:
            return False
            
        return True
    
    problem.addConstraint(time_available, ['start'])
    
    # Find solution
    solutions = problem.getSolutions()
    
    if solutions:
        solution = solutions[0]
        start_slot = solution['start']
        
        # Convert slot back to time
        start_hour = 9 + start_slot // 2
        start_minute = 30 if start_slot % 2 else 0
        
        end_slot = start_slot + meeting_duration
        end_hour = 9 + end_slot // 2
        end_minute = 30 if end_slot % 2 else 0
        
        # Format output
        start_time = f"{start_hour:02d}:{start_minute:02d}"
        end_time = f"{end_hour:02d}:{end_minute:02d}"
        
        print(f"Monday:{start_time}:{end_time}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()