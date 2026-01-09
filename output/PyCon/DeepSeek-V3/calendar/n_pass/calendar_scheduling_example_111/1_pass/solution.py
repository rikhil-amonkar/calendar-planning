from constraint import Problem

def main():
    # Create problem instance
    problem = Problem()
    
    # Define work hours (9:00 to 17:00 in 30-minute intervals)
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 30  # minutes
    
    # Generate all possible 30-minute time slots
    time_slots = []
    for start_minutes in range(work_start, work_end - meeting_duration + 1, 30):
        end_minutes = start_minutes + meeting_duration
        time_slots.append((start_minutes, end_minutes))
    
    # Add variable for time slot index
    problem.addVariable('time_slot', range(len(time_slots)))
    
    # Define constraints for each person's schedule
    def gregory_constraint(slot_idx):
        start, end = time_slots[slot_idx]
        # Gregory's busy times (in minutes)
        busy_times = [
            (9*60, 10*60),      # 9:00-10:00
            (10*60+30, 11*60+30), # 10:30-11:30
            (12*60+30, 13*60),   # 12:30-13:00
            (13*60+30, 14*60)    # 13:30-14:00
        ]
        return not any(busy_start <= start < busy_end or busy_start < end <= busy_end 
                      for busy_start, busy_end in busy_times)
    
    def christine_constraint(slot_idx):
        start, end = time_slots[slot_idx]
        # Christine's busy times (in minutes)
        busy_times = [
            (9*60, 11*60+30),   # 9:00-11:30
            (13*60+30, 17*60)   # 13:30-17:00
        ]
        return not any(busy_start <= start < busy_end or busy_start < end <= busy_end 
                      for busy_start, busy_end in busy_times)
    
    def vincent_constraint(slot_idx):
        start, end = time_slots[slot_idx]
        # Vincent's busy times (in minutes)
        busy_times = [
            (9*60, 9*60+30),    # 9:00-9:30
            (10*60+30, 12*60),  # 10:30-12:00
            (12*60+30, 14*60),  # 12:30-14:00
            (14*60+30, 17*60)   # 14:30-17:00
        ]
        return not any(busy_start <= start < busy_end or busy_start < end <= busy_end 
                      for busy_start, busy_end in busy_times)
    
    # Natalie has no constraints
    
    # Add constraints
    problem.addConstraint(gregory_constraint, ['time_slot'])
    problem.addConstraint(christine_constraint, ['time_slot'])
    problem.addConstraint(vincent_constraint, ['time_slot'])
    
    # Find solution
    solutions = problem.getSolutions()
    
    if solutions:
        # Get first solution
        slot_idx = solutions[0]['time_slot']
        start_minutes, end_minutes = time_slots[slot_idx]
        
        # Convert minutes to HH:MM format
        start_hour = start_minutes // 60
        start_minute = start_minutes % 60
        end_hour = end_minutes // 60
        end_minute = end_minutes % 60
        
        # Format output
        time_range = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
        print(f"Monday:{time_range}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()