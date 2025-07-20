from z3 import *

def main():
    # Convert all times to minutes from 9:00 (so 9:00 is 0, 17:00 is 480)
    min_start = 0
    max_end = 480
    meeting_duration = 30
    max_start = max_end - meeting_duration  # 450

    # Define busy intervals for each person in minutes
    andrea_busy = []
    jack_busy = [(0, 30), (300, 330)]
    madison_busy = [(30, 90), (240, 300), (360, 390), (450, 480)]
    rachel_busy = [(30, 90), (120, 150), (180, 270), (330, 390), (420, 480)]
    douglas_busy = [(0, 150), (180, 450)]
    ryan_busy = [(0, 30), (240, 300), (330, 480)]

    # Create Z3 solver and variable
    s = Int('s')
    solver = Solver()
    solver.add(s >= min_start, s <= max_start)

    # Function to add constraints for each person
    def add_busy_constraints(intervals):
        for a, b in intervals:
            solver.add(Or(s + meeting_duration <= a, s >= b))

    # Add constraints for each person
    add_busy_constraints(andrea_busy)
    add_busy_constraints(jack_busy)
    add_busy_constraints(madison_busy)
    add_busy_constraints(rachel_busy)
    add_busy_constraints(douglas_busy)
    add_busy_constraints(ryan_busy)

    # Check for solution
    if solver.check() == sat:
        model = solver.model()
        start_minutes = model[s].as_long()
        
        # Convert start_minutes to time string
        hours = 9 + start_minutes // 60
        minutes = start_minutes % 60
        start_time = f"{hours:02d}:{minutes:02d}"
        
        # Calculate end time
        end_minutes = start_minutes + meeting_duration
        end_hours = 9 + end_minutes // 60
        end_minutes_remainder = end_minutes % 60
        end_time = f"{end_hours:02d}:{end_minutes_remainder:02d}"
        
        # Output solution
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found")

if __name__ == '__main__':
    main()