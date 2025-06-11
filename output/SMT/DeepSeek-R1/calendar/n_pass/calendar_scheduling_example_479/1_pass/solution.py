from z3 import *

def main():
    # Initialize the solver
    s = Solver()
    
    # Meeting duration in minutes
    meeting_duration = 60
    
    # Total work hours in minutes (9:00 to 17:00 is 8 hours = 480 minutes)
    total_minutes = 480
    
    # Define the start time variable in minutes from 9:00
    S = Int('S')
    
    # Constraint: Start time must be within [0, total_minutes - meeting_duration]
    s.add(S >= 0)
    s.add(S <= total_minutes - meeting_duration)
    
    # Define busy intervals for each participant in minutes from 9:00
    # Format: list of (start_minute, end_minute) for each busy block
    busy_times = {
        'Joshua': [(120, 210), (270, 330), (450, 480)],
        'Jerry': [(0, 30), (90, 180), (210, 240), (270, 300), (330, 360), (390, 420)],
        'Jesse': [(0, 30), (90, 180), (210, 240), (330, 360), (390, 450)],
        'Kenneth': [(90, 210), (270, 300), (330, 360), (390, 420), (450, 480)]
    }
    
    # Participants with no busy times: Evelyn, Kevin, Gerald (no constraints needed)
    
    # Add constraints for each participant's busy intervals
    for participant, intervals in busy_times.items():
        for (a, b) in intervals:
            # The meeting [S, S+meeting_duration] should not overlap with [a, b)
            # This means: either meeting ends before a or meeting starts after b
            s.add(Or(S + meeting_duration <= a, S >= b))
    
    # Check for a solution
    if s.check() == sat:
        model = s.model()
        start_minutes = model[S].as_long()
        
        # Convert start_minutes back to time in HH:MM format
        start_hour = 9 + start_minutes // 60
        start_minute = start_minutes % 60
        
        # Calculate end time
        end_minutes = start_minutes + meeting_duration
        end_hour = 9 + end_minutes // 60
        end_minute = end_minutes % 60
        
        # Format the output
        start_time = f"{start_hour:02d}:{start_minute:02d}"
        end_time = f"{end_hour:02d}:{end_minute:02d}"
        
        print(f"Monday {start_time} to {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()