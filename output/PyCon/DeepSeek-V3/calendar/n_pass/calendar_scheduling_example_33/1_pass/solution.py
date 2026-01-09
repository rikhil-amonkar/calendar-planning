from constraint import Problem

def main():
    # Create problem instance
    problem = Problem()
    
    # Define work hours (9:00 to 17:00 in 30-minute intervals)
    work_start = 9 * 2  # 9:00 in half-hour units
    work_end = 17 * 2   # 17:00 in half-hour units
    
    # Define busy times for each person in half-hour units
    # Lisa's busy times
    lisa_busy = []
    lisa_busy.extend(range(9*2, 10*2))      # 9:00-10:00
    lisa_busy.extend(range(10*2+1, 11*2+1)) # 10:30-11:30
    lisa_busy.extend(range(12*2+1, 13*2))   # 12:30-13:00
    lisa_busy.extend(range(16*2, 16*2+1))   # 16:00-16:30
    
    # Bobby's busy times
    bobby_busy = []
    bobby_busy.extend(range(9*2, 9*2+1))    # 9:00-9:30
    bobby_busy.extend(range(10*2, 10*2+1))  # 10:00-10:30
    bobby_busy.extend(range(11*2+1, 12*2))  # 11:30-12:00
    bobby_busy.extend(range(15*2, 15*2+1))  # 15:00-15:30
    
    # Randy's busy times
    randy_busy = []
    randy_busy.extend(range(9*2+1, 10*2))   # 9:30-10:00
    randy_busy.extend(range(10*2+1, 11*2))  # 10:30-11:00
    randy_busy.extend(range(11*2+1, 12*2+1))# 11:30-12:30
    randy_busy.extend(range(13*2, 13*2+1))  # 13:00-13:30
    randy_busy.extend(range(14*2+1, 15*2+1))# 14:30-15:30
    randy_busy.extend(range(16*2, 16*2+1))  # 16:00-16:30
    
    # Define possible start times (30-minute meeting)
    possible_starts = range(work_start, work_end)
    
    # Add variable for meeting start time
    problem.addVariable('start_time', possible_starts)
    
    # Define constraint function
    def all_available(start):
        # Check if all participants are available for the 30-minute meeting
        meeting_slots = [start, start + 1]  # Two consecutive 30-minute slots
        
        # Check Lisa's availability
        for slot in meeting_slots:
            if slot in lisa_busy:
                return False
        
        # Check Bobby's availability and preference (avoid after 15:00)
        for slot in meeting_slots:
            if slot in bobby_busy:
                return False
        # Bobby prefers to avoid meetings after 15:00
        if start >= 15 * 2:
            return False
        
        # Check Randy's availability
        for slot in meeting_slots:
            if slot in randy_busy:
                return False
        
        return True
    
    # Add constraint
    problem.addConstraint(all_available, ['start_time'])
    
    # Find solutions
    solutions = problem.getSolutions()
    
    if solutions:
        # Get the first solution (earliest time)
        start_time_unit = solutions[0]['start_time']
        
        # Convert back to time format
        start_hour = start_time_unit // 2
        start_minute = 0 if start_time_unit % 2 == 0 else 30
        
        end_time_unit = start_time_unit + 1
        end_hour = end_time_unit // 2
        end_minute = 0 if end_time_unit % 2 == 0 else 30
        
        # Format output
        start_str = f"{start_hour:02d}:{start_minute:02d}"
        end_str = f"{end_hour:02d}:{end_minute:02d}"
        
        print(f"Monday:{start_str}:{end_str}")
    else:
        print("No available time slot found")

if __name__ == "__main__":
    main()