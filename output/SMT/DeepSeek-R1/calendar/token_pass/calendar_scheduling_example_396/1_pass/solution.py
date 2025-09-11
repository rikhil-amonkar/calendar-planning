from z3 import *

def main():
    # Convert time to minutes since 9:00
    def time_to_minutes(time_str):
        h, m = map(int, time_str.split(':'))
        return (h - 9) * 60 + m

    # Convert minutes back to HH:MM format
    def minutes_to_time(minutes):
        h = 9 + minutes // 60
        m = minutes % 60
        return f"{h:02d}:{m:02d}"

    # Meeting duration in minutes
    duration = 30
    
    # Work hours: 9:00 to 17:00 (480 minutes from 9:00)
    min_time = time_to_minutes("9:00")  # 0
    max_time = time_to_minutes("17:00") # 480
    max_start = max_time - duration
    
    # Create solver
    s = Solver()
    start = Int('start')
    s.add(start >= min_time, start <= max_start)
    
    # Define busy intervals for each participant (in minutes from 9:00)
    busy_intervals = {
        "Jack": [(0, 30), (300, 330)],
        "Madison": [(30, 90), (240, 300), (360, 390), (450, 480)],
        "Rachel": [(30, 90), (120, 150), (180, 270), (330, 390), (420, 480)],
        "Douglas": [(0, 150), (180, 450)],
        "Ryan": [(0, 30), (240, 300), (330, 480)]
    }
    
    # Add constraints for each participant
    for person, intervals in busy_intervals.items():
        for interval in intervals:
            b_start, b_end = interval
            # Meeting must not overlap with busy interval
            s.add(Or(start + duration <= b_start, start >= b_end))
    
    # Check for solution
    if s.check() == sat:
        model = s.model()
        start_val = model.eval(start).as_long()
        end_val = start_val + duration
        start_time = minutes_to_time(start_val)
        end_time = minutes_to_time(end_val)
        print(f"Monday {start_time}:{end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()