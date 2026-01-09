from constraint import Problem

def main():
    problem = Problem()
    
    # Define work hours (9:00 to 17:00 in 30-minute slots)
    work_start = 9 * 2  # 9:00 in half-hour units
    work_end = 17 * 2   # 17:00 in half-hour units
    
    # Convert busy times to half-hour slots
    # Adam: 14:00-15:00
    adam_busy = list(range(14*2, 15*2))
    
    # John: 13:00-13:30, 14:00-14:30, 15:30-16:00, 16:30-17:00
    john_busy = list(range(13*2, 13*2+1)) + list(range(14*2, 14*2+1)) + \
                list(range(15*2+1, 16*2)) + list(range(16*2+1, 17*2))
    
    # Stephanie: 9:30-10:00, 10:30-11:00, 11:30-16:00, 16:30-17:00
    stephanie_busy = list(range(9*2+1, 10*2)) + list(range(10*2+1, 11*2)) + \
                     list(range(11*2+1, 16*2)) + list(range(16*2+1, 17*2))
    
    # Anna: 9:30-10:00, 12:00-12:30, 13:00-15:30, 16:30-17:00
    anna_busy = list(range(9*2+1, 10*2)) + list(range(12*2, 12*2+1)) + \
                list(range(13*2, 15*2+1)) + list(range(16*2+1, 17*2))
    
    # Meeting duration: 30 minutes = 1 slot
    meeting_duration = 1
    
    # Define possible start times (in half-hour units)
    possible_starts = list(range(work_start, work_end - meeting_duration + 1))
    
    # Add variable for start time
    problem.addVariable('start_time', possible_starts)
    
    # Add constraints for each person's busy times
    def adam_available(start):
        end = start + meeting_duration
        return all(slot not in adam_busy for slot in range(start, end))
    
    def john_available(start):
        end = start + meeting_duration
        return all(slot not in john_busy for slot in range(start, end))
    
    def stephanie_available(start):
        end = start + meeting_duration
        return all(slot not in stephanie_busy for slot in range(start, end))
    
    def anna_available(start):
        end = start + meeting_duration
        # Additional constraint: Anna prefers after 14:30 (29 in half-hour units)
        return all(slot not in anna_busy for slot in range(start, end)) and start >= 29
    
    problem.addConstraint(adam_available, ['start_time'])
    problem.addConstraint(john_available, ['start_time'])
    problem.addConstraint(stephanie_available, ['start_time'])
    problem.addConstraint(anna_available, ['start_time'])
    
    # Find solution
    solutions = problem.getSolutions()
    
    if solutions:
        solution = solutions[0]
        start_slot = solution['start_time']
        
        # Convert slot back to time
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