from z3 import *

def main():
    # Convert a time string to minutes from 9:00
    def time_to_minutes(time_str):
        parts = time_str.split(':')
        hours = int(parts[0])
        minutes = int(parts[1])
        return (hours - 9) * 60 + minutes

    # Busy intervals for each participant (Andrea has none)
    participants_busy = [
        [("9:00", "9:30"), ("14:00", "14:30")],  # Jack
        [("9:30", "10:30"), ("13:00", "14:00"), ("15:00", "15:30"), ("16:30", "17:00")],  # Madison
        [("9:30", "10:30"), ("11:00", "11:30"), ("12:00", "13:30"), ("14:30", "15:30"), ("16:00", "17:00")],  # Rachel
        [("9:00", "11:30"), ("12:00", "16:30")],  # Douglas
        [("9:00", "9:30"), ("13:00", "14:00"), ("14:30", "17:00")]  # Ryan
    ]
    
    # Convert the busy intervals to minutes (relative to 9:00)
    busy_intervals_in_minutes = []
    for participant in participants_busy:
        converted_intervals = []
        for interval in participant:
            start_min = time_to_minutes(interval[0])
            end_min = time_to_minutes(interval[1])
            converted_intervals.append((start_min, end_min))
        busy_intervals_in_minutes.append(converted_intervals)
    
    # Initialize Z3 solver and variable
    solver = Solver()
    start_minutes = Int('start_minutes')
    
    # Constraints: start_minutes must be between 0 and 450 (inclusive) and a multiple of 30
    solver.add(start_minutes >= 0)
    solver.add(start_minutes <= 450)
    solver.add(start_minutes % 30 == 0)
    
    # For each participant, add non-overlap constraints for their busy intervals
    for participant_intervals in busy_intervals_in_minutes:
        constraints = []
        for (b_start, b_end) in participant_intervals:
            # The meeting [s, s+30) must not overlap with [b_start, b_end)
            # Condition: s+30 <= b_start OR b_end <= s
            c1 = (start_minutes + 30 <= b_start)
            c2 = (b_end <= start_minutes)
            constraints.append(Or(c1, c2))
        solver.add(And(*constraints))
    
    # Check for a solution
    if solver.check() == sat:
        model = solver.model()
        s_val = model.eval(start_minutes).as_long()
        
        # Convert start_minutes back to time string
        total_minutes = s_val
        hours = 9 + total_minutes // 60
        minutes = total_minutes % 60
        start_time = f"{hours}:{minutes:02d}"
        
        # Calculate end time
        end_minutes_val = s_val + 30
        end_hours = 9 + end_minutes_val // 60
        end_minutes = end_minutes_val % 60
        end_time = f"{end_hours}:{end_minutes:02d}"
        
        # Output the solution
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found")

if __name__ == '__main__':
    main()