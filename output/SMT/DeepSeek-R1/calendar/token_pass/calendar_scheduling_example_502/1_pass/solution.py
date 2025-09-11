from z3 import *

def main():
    # Initialize solver
    solver = Solver()
    
    # Define meeting duration in minutes
    meeting_duration = 30
    
    # Convert time to minutes from 9:00 (0 minutes) to 17:00 (480 minutes)
    work_start = 0
    work_end = 480
    
    # Jack's preference: avoid after 12:30 (210 minutes from 9:00)
    preference_end = 210
    
    # Define start time variable (in minutes from 9:00)
    start = Int('start')
    
    # Constraint: start must be within work hours
    solver.add(start >= work_start)
    solver.add(start <= work_end - meeting_duration)
    
    # Jack's busy intervals (start and end in minutes from 9:00)
    jack_busy = [(30, 90), (120, 150), (210, 240), (300, 330), (420, 450)]
    
    # Charlotte's busy intervals
    charlotte_busy = [(30, 60), (90, 180), (210, 270), (300, 420)]
    
    # Add constraints for Jack's busy times
    for busystart, busyend in jack_busy:
        solver.add(Or(start + meeting_duration <= busystart, start >= busyend))
    
    # Add constraints for Charlotte's busy times
    for busystart, busyend in charlotte_busy:
        solver.add(Or(start + meeting_duration <= busystart, start >= busyend))
    
    # Check for solution meeting Jack's preference (before 12:30)
    solver.push()
    solver.add(start + meeting_duration <= preference_end)
    if solver.check() == sat:
        model = solver.model()
        start_time = model.eval(start).as_long()
    else:
        solver.pop()
        if solver.check() == sat:
            model = solver.model()
            start_time = model.eval(start).as_long()
        else:
            print("No solution found")
            return
    
    # Convert start time back to HH:MM format
    total_minutes = start_time
    hours = total_minutes // 60
    minutes = total_minutes % 60
    start_str = f"{9 + hours:02d}:{minutes:02d}"
    
    # Calculate end time
    end_time_minutes = start_time + meeting_duration
    end_hours = end_time_minutes // 60
    end_minutes = end_time_minutes % 60
    end_str = f"{9 + end_hours:02d}:{end_minutes:02d}"
    
    # Output the result
    print(f"Monday:{start_str}:{end_str}")

if __name__ == "__main__":
    main()