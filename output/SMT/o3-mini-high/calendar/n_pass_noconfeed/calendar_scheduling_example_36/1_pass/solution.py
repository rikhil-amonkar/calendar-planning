from z3 import *

def minutes_to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def main():
    # Create the Z3 solver instance
    s = Solver()
    
    # Define the meeting start time as an integer representing minutes from midnight.
    start = Int('start')
    duration = 60  # meeting duration in minutes

    # Working hours on Monday: 09:00 (540) to 17:00 (1020)
    s.add(start >= 9 * 60)
    s.add(start + duration <= 17 * 60)
    
    # Denise's availability and preferences:
    # Denise is busy from 09:30 to 10:30 so the meeting must start no earlier than 10:30 (630 minutes).
    s.add(start >= 10 * 60 + 30)
    # Denise is busy from 12:00 to 13:00 so the meeting must end by 12:00 (720 minutes).
    s.add(start + duration <= 12 * 60)
    # Additionally, Denise does not want to meet after 12:30.
    # (This is automatically satisfied since meeting end <= 12:00.)

    # For completeness, we include non-overlap constraints for busy intervals.
    # Helper function to ensure the meeting does not overlap a busy interval [b_start, b_end)
    def no_overlap(b_start, b_end):
        return Or(start + duration <= b_start, start >= b_end)
    
    # Ryan's busy intervals:
    # Busy from 09:00 to 09:30
    s.add(no_overlap(9 * 60, 9 * 60 + 30))
    # Busy from 12:30 to 13:00
    s.add(no_overlap(12 * 60 + 30, 13 * 60))
    
    # Denise's additional busy intervals:
    # Busy from 09:30 to 10:30
    s.add(no_overlap(9 * 60 + 30, 10 * 60 + 30))
    # Busy from 12:00 to 13:00
    s.add(no_overlap(12 * 60, 13 * 60))
    # Busy from 14:30 to 16:30; though given the other constraints, the meeting will be scheduled well before this.
    s.add(no_overlap(14 * 60 + 30, 16 * 60 + 30))
    
    # Ruth has no meetings, so no additional constraints are needed for her.

    # Check for a solution.
    if s.check() == sat:
        model = s.model()
        meeting_start = model[start].as_long()
        meeting_end = meeting_start + duration
        
        start_str = minutes_to_time_str(meeting_start)
        end_str = minutes_to_time_str(meeting_end)
        
        print(f"Monday {start_str}:{end_str}")
    else:
        print("No solution found.")

if __name__ == '__main__':
    main()