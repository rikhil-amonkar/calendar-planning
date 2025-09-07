from z3 import Solver, Int, Or, Implies, sat

def main():
    solver = Solver()
    
    # Use an integer to represent the day: 0 -> Monday, 1 -> Tuesday.
    day = Int("day")
    # Meeting start time is represented as minutes offset from 9:00.
    # Given work hours 9:00 to 17:00 and a meeting duration of 60 minutes,
    # the start time must be between 0 and 420 (i.e., 9:00 to 16:00).
    start = Int("start")
    meeting_duration = 60

    # Allowed values for day and start time.
    solver.add(Or(day == 0, day == 1))
    solver.add(start >= 0, start <= 420)
    
    # Busy intervals are represented in minutes relative to 9:00.
    # Patricia's busy times:
    # Monday: 10:00-10:30 => [60,90], 11:30-12:00 => [150,180], 
    #         13:00-13:30 => [240,270], 14:30-15:30 => [330,390], 
    #         16:00-16:30 => [420,450]
    busy_patricia_monday = [(60, 90), (150, 180), (240, 270), (330, 390), (420, 450)]
    # Tuesday: 10:00-10:30 => [60,90], 11:00-12:00 => [120,180],
    #          14:00-16:00 => [300,420], 16:30-17:00 => [450,480]
    busy_patricia_tuesday = [(60, 90), (120, 180), (300, 420), (450, 480)]
    
    # Jesse's busy times:
    # Monday: Entire work day 9:00-17:00 => [0,480]
    busy_jesse_monday = [(0, 480)]
    # Tuesday: 11:00-11:30 => [120,150], 12:00-12:30 => [180,210],
    #          13:00-14:00 => [240,300], 14:30-15:00 => [330,360],
    #          15:30-17:00 => [390,480]
    busy_jesse_tuesday = [(120, 150), (180, 210), (240, 300), (330, 360), (390, 480)]
    
    # Function: for a given busy interval (busy_start, busy_end), enforce that if the meeting is on that day,
    # then the meeting [start, start+meeting_duration] does not overlap the busy interval.
    def add_busy_constraints(day_value, busy_intervals):
        for (busy_start, busy_end) in busy_intervals:
            solver.add(Implies(day == day_value, Or(start + meeting_duration <= busy_start, start >= busy_end)))
    
    # Add Patricia's constraints.
    add_busy_constraints(0, busy_patricia_monday)
    add_busy_constraints(1, busy_patricia_tuesday)
    
    # Add Jesse's constraints.
    add_busy_constraints(0, busy_jesse_monday)
    add_busy_constraints(1, busy_jesse_tuesday)
    
    # Check for a solution.
    if solver.check() == sat:
        model = solver.model()
        chosen_day = model[day].as_long()  # 0 for Monday, 1 for Tuesday
        chosen_start = model[start].as_long()
        chosen_end = chosen_start + meeting_duration
        
        # Function to convert offset minutes from 9:00 into an (hour, minute) tuple.
        def get_time(offset):
            total_minutes = 9 * 60 + offset
            hr = total_minutes // 60
            mn = total_minutes % 60
            return hr, mn
        
        start_hr, start_min = get_time(chosen_start)
        end_hr, end_min = get_time(chosen_end)
        
        # Map the day number back to the day name.
        day_str = "Monday" if chosen_day == 0 else "Tuesday"
        # Format the time string as "HH:MM:HH:MM" (start:end)
        time_str = f"{start_hr:02d}:{start_min:02d}:{end_hr:02d}:{end_min:02d}"
        print(f"{day_str} {time_str}")
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()