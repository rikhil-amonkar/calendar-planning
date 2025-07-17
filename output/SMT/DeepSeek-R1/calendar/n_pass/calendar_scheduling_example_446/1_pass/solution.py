from z3 import *

def main():
    # Initialize solver
    s = Solver()
    # Start time in minutes from 9:00 (0 to 450 inclusive)
    start = Int('start')
    s.add(start >= 0, start <= 450)  # 450 minutes = 16:30, meeting ends at 17:00

    # Define busy intervals for each participant (in minutes from 9:00)
    busy_times = {
        'Megan': [(0, 30), (60, 120), (180, 210)],
        'Christine': [(0, 30), (150, 180), (240, 300), (390, 450)],
        'Sara': [(150, 180), (330, 360)],
        'Bruce': [(30, 60), (90, 180), (210, 300), (330, 360), (390, 450)],
        'Kathryn': [(60, 390), (420, 450)],
        'Billy': [(0, 30), (120, 150), (180, 300), (330, 390)],
        # Gabriel is free all day, no constraints
    }

    # Add constraints for each participant's busy intervals
    for participant, intervals in busy_times.items():
        for (busy_start, busy_end) in intervals:
            s.add(Or(start + 30 <= busy_start, start >= busy_end))

    # Check for a solution
    if s.check() == sat:
        model = s.model()
        start_minutes = model[start].as_long()
        
        # Convert start_minutes to time string
        total_minutes = start_minutes
        hours = 9 + total_minutes // 60
        minutes = total_minutes % 60
        start_time = f"{hours:02d}:{minutes:02d}"
        
        # Calculate end time
        end_minutes = start_minutes + 30
        hours_end = 9 + end_minutes // 60
        minutes_end = end_minutes % 60
        end_time = f"{hours_end:02d}:{minutes_end:02d}"
        
        # Output the solution
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()