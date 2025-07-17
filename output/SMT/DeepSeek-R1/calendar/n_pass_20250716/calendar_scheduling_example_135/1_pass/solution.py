from z3 import *

def main():
    # Create solver
    s = Solver()
    
    # Define the start time in minutes from 9:00
    start = Int('start')
    
    # Meeting duration in minutes
    duration = 30
    
    # Work day end: 17:00 is 480 minutes from 9:00
    work_end = 480
    
    # Constraint: meeting must start between 0 (9:00) and 450 (16:30) inclusive
    s.add(start >= 0)
    s.add(start + duration <= work_end)  # Ends by 17:00
    
    # Busy intervals for each participant (in minutes from 9:00)
    # Eric has no meetings, so no constraints
    
    # Ashley: [10:00-10:30), [11:00-12:00), [12:30-13:00), [15:00-16:00)
    ashley_busy = [(60, 90), (120, 180), (210, 240), (360, 420)]
    
    # Ronald: [9:00-9:30), [10:00-11:30), [12:30-14:00), [14:30-17:00)
    ronald_busy = [(0, 30), (60, 150), (210, 300), (330, 480)]
    
    # Larry: [9:00-12:00), [13:00-17:00)
    larry_busy = [(0, 180), (240, 480)]
    
    # Function to add constraints for a participant's busy intervals
    def add_busy_constraints(busy_intervals):
        for (busy_start, busy_end) in busy_intervals:
            # The meeting must not overlap with [busy_start, busy_end)
            s.add(Or(start + duration <= busy_start, start >= busy_end))
    
    # Add constraints for Ashley, Ronald, and Larry
    add_busy_constraints(ashley_busy)
    add_busy_constraints(ronald_busy)
    add_busy_constraints(larry_busy)
    
    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        start_minutes = m.evaluate(start).as_long()
        
        # Convert start_minutes back to time string
        total_minutes = start_minutes
        hours = 9 + total_minutes // 60
        minutes = total_minutes % 60
        start_time = f"{hours:02d}:{minutes:02d}"
        
        # Calculate end time
        end_minutes = start_minutes + duration
        end_hours = 9 + end_minutes // 60
        end_minutes_remainder = end_minutes % 60
        end_time = f"{end_hours:02d}:{end_minutes_remainder:02d}"
        
        # Print the solution
        print(f"Monday, {start_time}, {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()