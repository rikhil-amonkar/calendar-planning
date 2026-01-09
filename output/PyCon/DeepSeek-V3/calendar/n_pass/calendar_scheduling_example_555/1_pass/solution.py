from constraint import Problem

def main():
    problem = Problem()
    
    # Define the time slots in 30-minute increments from 9:00 to 17:00
    time_slots = []
    for hour in range(9, 17):
        for minute in [0, 30]:
            if hour == 16 and minute == 30:
                continue  # Skip 16:30 since end time is 17:00
            start_time = f"{hour:02d}:{minute:02d}"
            end_hour = hour if minute == 0 else hour + 1
            end_minute = 30 if minute == 0 else 0
            end_time = f"{end_hour:02d}:{end_minute:02d}"
            time_slots.append(f"{start_time}:{end_time}")
    
    # Add variable for the meeting time slot
    problem.addVariable("meeting_time", time_slots)
    
    # Define constraints
    def evelyn_available(time_slot):
        # Evelyn has no meetings but doesn't want to meet after 13:00
        start_time = time_slot.split(':')[0]
        hour = int(start_time.split(':')[0])
        return hour < 13
    
    def randy_available(time_slot):
        # Randy's busy periods: 9:00-10:30, 11:00-15:30, 16:00-17:00
        start_time = time_slot.split(':')[0]
        end_time = time_slot.split(':')[2]
        
        start_hour, start_minute = map(int, start_time.split(':'))
        end_hour, end_minute = map(int, end_time.split(':'))
        
        # Convert to minutes for easier comparison
        start_total = start_hour * 60 + start_minute
        end_total = end_hour * 60 + end_minute
        
        # Check if the meeting overlaps with any busy period
        busy_periods = [
            (9*60, 10*60+30),    # 9:00-10:30
            (11*60, 15*60+30),   # 11:00-15:30  
            (16*60, 17*60)       # 16:00-17:00
        ]
        
        for busy_start, busy_end in busy_periods:
            if not (end_total <= busy_start or start_total >= busy_end):
                return False
        return True
    
    problem.addConstraint(evelyn_available, ["meeting_time"])
    problem.addConstraint(randy_available, ["meeting_time"])
    
    # Find solution
    solutions = problem.getSolutions()
    
    if solutions:
        meeting_time = solutions[0]["meeting_time"]
        print(f"Monday:{meeting_time}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()