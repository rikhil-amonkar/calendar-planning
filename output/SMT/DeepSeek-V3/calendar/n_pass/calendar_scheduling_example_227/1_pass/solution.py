from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()
    
    # Define the possible start times (in minutes from 9:00)
    start_time = Int('start_time')
    
    # Meeting duration is 30 minutes
    duration = 30
    
    # Total working hours from 9:00 to 17:00 is 8 hours = 480 minutes
    min_time = 9 * 60  # 9:00 in minutes
    max_time = 17 * 60 - duration  # 16:30 is the latest possible start time
    
    # Constraint: start_time must be within working hours
    s.add(start_time >= min_time)
    s.add(start_time <= max_time)
    
    # Constraint: start_time must be in 30-minute increments (0, 30, 60, ...)
    s.add(start_time % 30 == 0)
    
    # Define busy intervals for each participant (in minutes from 0:00)
    # Each interval is (start, end)
    
    # Natalie: open all day
    natalie_busy = []
    
    # David: busy 11:30-12:00, 14:30-15:00; prefers not before 14:00
    david_busy = [(11*60 + 30, 12*60), (14*60 + 30, 15*60)]
    # David's preference: meeting should start at or after 14:00
    s.add(start_time >= 14 * 60)
    
    # Douglas: busy 9:30-10:00, 11:30-12:00, 13:00-13:30, 14:30-15:00
    douglas_busy = [(9*60 + 30, 10*60), (11*60 + 30, 12*60), (13*60, 13*60 + 30), (14*60 + 30, 15*60)]
    
    # Ralph: busy 9:00-9:30, 10:00-11:00, 11:30-12:30, 13:30-15:00, 15:30-16:00, 16:30-17:00
    ralph_busy = [(9*60, 9*60 + 30), (10*60, 11*60), (11*60 + 30, 12*60 + 30),
                  (13*60 + 30, 15*60), (15*60 + 30, 16*60), (16*60 + 30, 17*60)]
    
    # Jordan: busy 9:00-10:00, 12:00-12:30, 13:00-13:30, 14:30-15:00, 15:30-17:00
    jordan_busy = [(9*60, 10*60), (12*60, 12*60 + 30), (13*60, 13*60 + 30),
                   (14*60 + 30, 15*60), (15*60 + 30, 17*60)]
    
    # Function to check if the meeting overlaps with any busy interval
    def no_overlap(meeting_start, meeting_end, intervals):
        return And([Or(meeting_end <= interval_start, meeting_start >= interval_end) 
                    for interval_start, interval_end in intervals])
    
    meeting_end = start_time + duration
    
    # Add constraints for each participant's busy times
    s.add(no_overlap(start_time, meeting_end, natalie_busy))  # Natalie has no busy times
    s.add(no_overlap(start_time, meeting_end, david_busy))
    s.add(no_overlap(start_time, meeting_end, douglas_busy))
    s.add(no_overlap(start_time, meeting_end, ralph_busy))
    s.add(no_overlap(start_time, meeting_end, jordan_busy))
    
    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        start_minutes = m.evaluate(start_time).as_long()
        
        # Convert minutes back to HH:MM format
        start_hh = start_minutes // 60
        start_mm = start_minutes % 60
        end_minutes = start_minutes + duration
        end_hh = end_minutes // 60
        end_mm = end_minutes % 60
        
        # Format the output
        print("SOLUTION:")
        print(f"Day: Monday")
        print(f"Start Time: {start_hh:02d}:{start_mm:02d}")
        print(f"End Time: {end_hh:02d}:{end_mm:02d}")
    else:
        print("No solution found")

solve_scheduling()