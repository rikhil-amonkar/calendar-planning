from z3 import *

def solve_scheduling():
    # Initialize the solver
    solver = Solver()
    
    # Define the start time in minutes from 9:00 (0 = 9:00, 60 = 10:00, etc.)
    start_time = Int('start_time')
    
    # Meeting duration is 1 hour (60 minutes)
    duration = 60
    
    # Total working hours from 9:00 to 17:00 is 8 hours = 480 minutes
    max_time = 480
    
    # Constraint: start_time must be >= 0 and <= max_time - duration
    solver.add(start_time >= 0)
    solver.add(start_time <= max_time - duration)
    
    # Define the existing meetings for each participant in minutes from 9:00
    # Danielle's meetings: 9:00-10:00 (0-60), 10:30-11:00 (90-120), 14:30-15:00 (330-360), 15:30-16:00 (390-420), 16:30-17:00 (450-480)
    danielle_meetings = [(0, 60), (90, 120), (330, 360), (390, 420), (450, 480)]
    
    # Bruce's meetings: 11:00-11:30 (120-150), 12:30-13:00 (210-240), 14:00-14:30 (300-330), 15:30-16:00 (390-420)
    bruce_meetings = [(120, 150), (210, 240), (300, 330), (390, 420)]
    
    # Eric's meetings: 9:00-9:30 (0-30), 10:00-11:00 (60-120), 11:30-13:00 (150-240), 14:30-15:30 (330-390)
    eric_meetings = [(0, 30), (60, 120), (150, 240), (330, 390)]
    
    # Function to add no-overlap constraints for a participant's meetings
    def add_no_overlap(meetings):
        for (m_start, m_end) in meetings:
            # The meeting does not overlap with m_start..m_end
            # So either our meeting ends before m_start or starts after m_end
            solver.add(Or(start_time + duration <= m_start, start_time >= m_end))
    
    # Add constraints for each participant
    add_no_overlap(danielle_meetings)
    add_no_overlap(bruce_meetings)
    add_no_overlap(eric_meetings)
    
    # Check for a solution
    if solver.check() == sat:
        model = solver.model()
        start_minutes = model.evaluate(start_time).as_long()
        
        # Convert start_minutes back to HH:MM format
        hours = 9 + start_minutes // 60
        minutes = start_minutes % 60
        start_time_str = f"{hours:02d}:{minutes:02d}"
        
        end_minutes = start_minutes + duration
        end_hours = 9 + end_minutes // 60
        end_minutes = end_minutes % 60
        end_time_str = f"{end_hours:02d}:{end_minutes:02d}"
        
        # Print the solution in the required format
        print("SOLUTION:")
        print(f"Day: Monday")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found")

solve_scheduling()