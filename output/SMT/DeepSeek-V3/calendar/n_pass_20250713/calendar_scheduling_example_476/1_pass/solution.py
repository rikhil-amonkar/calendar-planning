from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()
    
    # Define the start time in minutes from 9:00 (0 is 9:00, 480 is 17:00)
    start_time = Int('start_time')
    meeting_duration = 30
    end_time = start_time + meeting_duration
    
    # Constraints for the meeting to be within work hours (9:00-17:00)
    s.add(start_time >= 0)
    s.add(end_time <= 480)  # 8 hours * 60 minutes = 480
    
    # Roger's preference: not before 12:30 (which is 210 minutes from 9:00)
    s.add(start_time >= 210)  # 12:30 is 3.5 hours after 9:00 -> 3.5*60=210
    
    # Define each participant's busy slots in minutes from 9:00
    # Each slot is (start, end) in minutes
    
    # Kathleen: 14:30-15:30 (330 to 390)
    kathleen_busy = [(330, 390)]
    # Carolyn: 12:00-12:30 (180 to 210), 13:00-13:30 (240 to 270)
    carolyn_busy = [(180, 210), (240, 270)]
    # Cheryl: 9:00-9:30 (0 to 30), 10:00-11:30 (60 to 150), 12:30-13:30 (210 to 270), 14:00-17:00 (300 to 480)
    cheryl_busy = [(0, 30), (60, 150), (210, 270), (300, 480)]
    # Virginia: 9:30-11:30 (30 to 150), 12:00-12:30 (180 to 210), 13:00-13:30 (240 to 270), 14:30-15:30 (330 to 390), 16:00-17:00 (420 to 480)
    virginia_busy = [(30, 150), (180, 210), (240, 270), (330, 390), (420, 480)]
    # Angela: 9:30-10:00 (30 to 60), 10:30-11:30 (90 to 150), 12:00-12:30 (180 to 210), 13:00-13:30 (240 to 270), 14:00-16:30 (300 to 450)
    angela_busy = [(30, 60), (90, 150), (180, 210), (240, 270), (300, 450)]
    
    # Daniel and Roger are free all day, except Roger's preference handled earlier
    
    # Function to add constraints that the meeting does not overlap with any busy slots
    def add_no_overlap_constraints(busy_slots):
        for (busy_start, busy_end) in busy_slots:
            s.add(Or(end_time <= busy_start, start_time >= busy_end))
    
    # Add constraints for each participant
    add_no_overlap_constraints(kathleen_busy)
    add_no_overlap_constraints(carolyn_busy)
    add_no_overlap_constraints(cheryl_busy)
    add_no_overlap_constraints(virginia_busy)
    add_no_overlap_constraints(angela_busy)
    
    # Check if a solution exists
    if s.check() == sat:
        model = s.model()
        start_minutes = model[start_time].as_long()
        
        # Convert start_minutes back to HH:MM format
        hours = 9 + (start_minutes // 60)
        minutes = start_minutes % 60
        start_time_str = f"{hours:02d}:{minutes:02d}"
        
        end_minutes = start_minutes + 30
        end_hours = 9 + (end_minutes // 60)
        end_minutes_remainder = end_minutes % 60
        end_time_str = f"{end_hours:02d}:{end_minutes_remainder:02d}"
        
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found")

solve_scheduling()