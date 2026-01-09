from constraint import Problem

def main():
    problem = Problem()
    
    # Define the time slots in 30-minute increments from 9:00 to 17:00
    time_slots = []
    for hour in range(9, 17):
        for minute in [0, 30]:
            if hour == 16 and minute == 30:
                continue  # End at 17:00, so skip 16:30-17:00
            start_time = f"{hour:02d}:{minute:02d}"
            end_hour = hour if minute == 0 else hour + 1
            end_minute = 30 if minute == 0 else 0
            end_time = f"{end_hour:02d}:{end_minute:02d}"
            time_slots.append((start_time, end_time))
    
    # Add variable for meeting start time (index in time_slots)
    problem.addVariable("meeting_time", range(len(time_slots)))
    
    # Margaret's busy slots
    margaret_busy = [
        ("09:00", "10:00"), ("10:30", "11:00"), ("11:30", "12:00"),
        ("13:00", "13:30"), ("15:00", "15:30")
    ]
    
    # Donna's busy slots
    donna_busy = [
        ("14:30", "15:00"), ("16:00", "16:30")
    ]
    
    # Helen's busy slots
    helen_busy = [
        ("09:00", "09:30"), ("10:00", "11:30"), ("13:00", "14:00"),
        ("14:30", "15:00"), ("15:30", "17:00")
    ]
    
    # Helen's constraint: doesn't want to meet after 13:30
    helen_no_after_1330 = [("13:30", "17:00")]
    
    def is_available(person_busy, meeting_slot):
        meeting_start, meeting_end = meeting_slot
        for busy_start, busy_end in person_busy:
            # Check if meeting overlaps with busy slot
            if not (meeting_end <= busy_start or meeting_start >= busy_end):
                return False
        return True
    
    def constraint(meeting_idx):
        meeting_slot = time_slots[meeting_idx]
        
        # Check Margaret's availability
        if not is_available(margaret_busy, meeting_slot):
            return False
            
        # Check Donna's availability
        if not is_available(donna_busy, meeting_slot):
            return False
            
        # Check Helen's availability
        if not is_available(helen_busy, meeting_slot):
            return False
            
        # Check Helen's preference (no meetings after 13:30)
        if not is_available(helen_no_after_1330, meeting_slot):
            return False
            
        return True
    
    problem.addConstraint(constraint, ["meeting_time"])
    
    solutions = problem.getSolutions()
    
    if solutions:
        meeting_idx = solutions[0]["meeting_time"]
        start_time, end_time = time_slots[meeting_idx]
        print(f"Monday:{start_time}:{end_time}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()