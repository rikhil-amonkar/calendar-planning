from z3 import *

def main():
    # Initialize solver
    s = Solver()
    
    # Meeting duration in minutes
    meeting_duration = 30
    
    # Work hours: 9:00 to 17:00 (8 hours = 480 minutes)
    work_start = 0
    work_end = 480
    
    # Define start time variable (in minutes from 9:00)
    start = Int('start')
    
    # Constraint: Start time must be within work hours and allow meeting to end by 17:00
    s.add(start >= work_start)
    s.add(start <= work_end - meeting_duration)
    
    # Busy intervals in minutes from 9:00
    denise_busy = [(180, 210), (390, 420)]  # 12:00-12:30, 15:30-16:00
    angela_busy = []  # No meetings
    natalie_busy = [(0, 150), (180, 240), (300, 330), (360, 480)]  # 9:00-11:30, 12:00-13:00, 14:00-14:30, 15:00-17:00
    
    # Function to add no-overlap constraints for a person's busy intervals
    def add_no_overlap_constraints(busy_intervals):
        for interval in busy_intervals:
            b_start, b_end = interval
            # Meeting must not overlap with busy interval: it must end before or start after
            s.add(Or(start + meeting_duration <= b_start, start >= b_end))
    
    # Add constraints for each participant
    add_no_overlap_constraints(denise_busy)
    add_no_overlap_constraints(angela_busy)
    add_no_overlap_constraints(natalie_busy)
    
    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        start_minutes = m.evaluate(start).as_long()
        
        # Convert start minutes to time string
        start_hour = 9 + start_minutes // 60
        start_minute = start_minutes % 60
        end_minutes = start_minutes + meeting_duration
        end_hour = 9 + end_minutes // 60
        end_minute = end_minutes % 60
        
        # Format the output
        time_str = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
        print("Monday")
        print(time_str)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()