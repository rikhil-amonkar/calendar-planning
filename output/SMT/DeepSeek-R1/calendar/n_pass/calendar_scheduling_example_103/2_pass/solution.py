from z3 import Int, Solver, Or, And, sat

def main():
    s = Solver()
    
    # Define the start time in minutes from 9:00
    S = Int('S')
    
    # Meeting duration in minutes
    duration = 30
    
    # Total work day in minutes: 9:00 (0) to 17:00 (480)
    work_start = 0
    work_end = 480
    
    # Constraints: meeting must be within work hours
    s.add(S >= work_start)
    s.add(S + duration <= work_end)
    
    # Blocked intervals for each participant (in minutes from 9:00)
    diane_blocked = [(30, 60), (330, 360)]       # 9:30-10:00, 14:30-15:00
    jack_blocked = [(270, 300), (330, 360)]      # 13:30-14:00, 14:30-15:00
    eugene_blocked = [(0, 60), (90, 150), (180, 330), (360, 450)]    # 9:00-10:00, 10:30-11:30, 12:00-14:30, 15:00-16:30
    patricia_blocked = [(30, 90), (120, 180), (150, 300), (360, 450)] # 9:30-10:30, 11:00-12:00, 12:30-14:00, 15:00-16:30
    
    # Function to add constraints for each participant's blocked intervals
    def add_participant_constraints(intervals):
        constraints = []
        for start, end in intervals:
            constraints.append(Or(S + duration <= start, S >= end))
        s.add(And(constraints))
    
    # Add constraints for each participant
    add_participant_constraints(diane_blocked)
    add_participant_constraints(jack_blocked)
    add_participant_constraints(eugene_blocked)
    add_participant_constraints(patricia_blocked)
    
    # Check for a solution
    if s.check() == sat:
        model = s.model()
        start_minutes = model[S].as_long()
        
        # Convert start_minutes back to time string
        hours = 9 + start_minutes // 60
        minutes = start_minutes % 60
        start_time = f"{hours}:{minutes:02d}"
        
        # Calculate end time
        end_minutes = start_minutes + duration
        end_hours = 9 + end_minutes // 60
        end_minutes = end_minutes % 60
        end_time = f"{end_hours}:{end_minutes:02d}"
        
        print(f"Monday {start_time} to {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()