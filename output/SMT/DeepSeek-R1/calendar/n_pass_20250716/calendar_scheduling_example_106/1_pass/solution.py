from z3 import *

def main():
    # Initialize solver
    s = Solver()
    
    # Meeting duration in minutes
    duration = 60
    
    # Total available time window: 9:00 (0 min) to 17:00 (480 min)
    total_minutes = 480
    S = Int('S')  # Start time in minutes from 9:00
    
    # Constraint: Start time must be within [0, 420] to allow for 60-minute meeting
    s.add(S >= 0)
    s.add(S <= total_minutes - duration)
    
    # Define blocked time intervals for each participant in minutes from 9:00
    olivia_blocked = [(210, 270), (330, 360), (450, 480)]
    anna_blocked = []  # No meetings
    virginia_blocked = [(0, 60), (150, 420), (450, 480)]
    paul_blocked = [(0, 30), (120, 150), (240, 300), (330, 420), (450, 480)]
    
    # Function to add constraints for a participant's blocked intervals
    def add_participant_constraints(blocked_intervals):
        constraints = []
        for start, end in blocked_intervals:
            # The meeting must not overlap: either ends before the block starts or starts after the block ends
            constraints.append(Or(S + duration <= start, S >= end))
        s.add(And(constraints))
    
    # Add constraints for each participant
    add_participant_constraints(olivia_blocked)
    add_participant_constraints(anna_blocked)  # No constraints if empty
    add_participant_constraints(virginia_blocked)
    add_participant_constraints(paul_blocked)
    
    # Check for a solution
    if s.check() == sat:
        model = s.model()
        start_minutes = model[S].as_long()
        
        # Convert minutes back to HH:MM format
        hours = 9 + start_minutes // 60
        minutes = start_minutes % 60
        start_time = f"{hours:02d}:{minutes:02d}"
        
        end_minutes = start_minutes + duration
        end_hours = 9 + end_minutes // 60
        end_minutes = end_minutes % 60
        end_time = f"{end_hours:02d}:{end_minutes:02d}"
        
        print(f"Monday {start_time} to {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()