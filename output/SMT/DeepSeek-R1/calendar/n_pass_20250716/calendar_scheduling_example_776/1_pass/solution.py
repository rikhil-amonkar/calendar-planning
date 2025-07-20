from z3 import *

def main():
    # Initialize the solver and the start time variable
    start = Int('start')
    solver = Solver()
    
    # Total minutes in three days (each day 480 minutes: 9:00 to 17:00)
    total_minutes = 480 * 3
    meeting_duration = 30
    
    # Constraint: start time must be in [0, total_minutes - meeting_duration]
    solver.add(start >= 0)
    solver.add(start <= total_minutes - meeting_duration)
    
    # Day and time within day
    day = start / 480  # Integer division to get day index
    time_in_day = start % 480
    
    # Constraint: meeting must end by 17:00 on the chosen day
    solver.add(time_in_day + meeting_duration <= 480)
    
    # John's constraint: on Monday (day 0), meeting must end by 14:30 (330 minutes from 9:00)
    solver.add(If(day == 0, time_in_day <= 300, True))
    
    # Jennifer's busy intervals per day (each interval [start_min, end_min) in minutes from 9:00)
    busy_intervals = {
        0: [(0, 120), (150, 240), (270, 330), (360, 480)],   # Monday
        1: [(0, 150), (180, 480)],                           # Tuesday
        2: [(0, 150), (180, 210), (240, 300), (330, 420), (450, 480)]  # Wednesday
    }
    
    # Add constraints for each busy interval
    for day_index, intervals in busy_intervals.items():
        for s, e in intervals:
            # The meeting must not overlap the interval [s, e)
            no_overlap = Or(time_in_day + meeting_duration <= s, time_in_day >= e)
            # Apply only if the meeting is on this day
            solver.add(If(day == day_index, no_overlap, True))
    
    # Check for a solution
    if solver.check() == sat:
        model = solver.model()
        start_val = model.eval(start).as_long()
        
        # Determine the day and time within the day
        day_index = start_val // 480
        time_in_day_val = start_val % 480
        
        # Convert time_in_day to hours and minutes
        hours = 9 + time_in_day_val // 60
        minutes = time_in_day_val % 60
        end_time_val = time_in_day_val + meeting_duration
        end_hours = 9 + end_time_val // 60
        end_minutes = end_time_val % 60
        
        # Format the time strings
        start_time_str = f"{hours:02d}:{minutes:02d}"
        end_time_str = f"{end_hours:02d}:{end_minutes:02d}"
        days = ["Monday", "Tuesday", "Wednesday"]
        day_str = days[day_index]
        
        # Output the solution
        print(f"Day: {day_str}")
        print(f"Start: {start_time_str}")
        print(f"End: {end_time_str}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()