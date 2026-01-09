from constraint import Problem

def main():
    # Create a problem instance
    problem = Problem()
    
    # Define work hours (9:00 to 17:00 in 30-minute intervals)
    time_slots = []
    for hour in range(9, 17):
        for minute in [0, 30]:
            if hour == 16 and minute == 30:
                continue  # Last slot ends at 17:00
            start_time = f"{hour:02d}:{minute:02d}"
            end_hour = hour if minute == 0 else hour + 1
            end_minute = 30 if minute == 0 else 0
            end_time = f"{end_hour:02d}:{end_minute:02d}"
            time_slots.append((start_time, end_time))
    
    # Add variable for meeting start time (as index in time_slots)
    problem.addVariable('meeting_time', range(len(time_slots)))
    
    # Define busy times for each person
    busy_slots = {
        'Stephanie': [(11, 0, 11, 30), (14, 30, 15, 0)],
        'Joe': [(9, 0, 9, 30), (10, 0, 12, 0), (12, 30, 13, 0), (14, 0, 17, 0)],
        'Diana': [(9, 0, 10, 30), (11, 30, 12, 0), (13, 0, 14, 0), (14, 30, 15, 30), (16, 0, 17, 0)],
        'Deborah': [(9, 0, 10, 0), (10, 30, 12, 0), (12, 30, 13, 0), (13, 30, 14, 0), (14, 30, 15, 30), (16, 0, 16, 30)]
    }
    
    # Tyler, Kelly, Hannah have no meetings
    
    # Constraint: Meeting cannot overlap with anyone's busy time
    def time_constraint(meeting_idx):
        meeting_start, meeting_end = time_slots[meeting_idx]
        start_hour, start_minute = map(int, meeting_start.split(':'))
        end_hour, end_minute = map(int, meeting_end.split(':'))
        
        # Check each person's busy times
        for person, busy_times in busy_slots.items():
            for busy_start_h, busy_start_m, busy_end_h, busy_end_m in busy_times:
                # Convert to minutes for easier comparison
                meeting_start_min = start_hour * 60 + start_minute
                meeting_end_min = end_hour * 60 + end_minute
                busy_start_min = busy_start_h * 60 + busy_start_m
                busy_end_min = busy_end_h * 60 + busy_end_m
                
                # Check for overlap
                if not (meeting_end_min <= busy_start_min or meeting_start_min >= busy_end_min):
                    return False
        
        return True
    
    problem.addConstraint(time_constraint, ['meeting_time'])
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if solutions:
        # Get the first solution
        meeting_idx = solutions[0]['meeting_time']
        start_time, end_time = time_slots[meeting_idx]
        print(f"Monday:{start_time}:{end_time}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()