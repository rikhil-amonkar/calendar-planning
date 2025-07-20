from z3 import *

def main():
    s = Solver()
    start = Int('start')

    # Constraints: meeting must be within 9:00 to 17:00, but also must end by 14:30 (330 minutes from 9:00)
    s.add(start >= 0)
    s.add(start + 60 <= 330)  # 330 minutes = 14:30

    # Busy times in minutes from 9:00
    anthony_busy = [(30, 60), (180, 240), (420, 450)]
    pamela_busy = [(30, 60), (450, 480)]
    zachary_busy = [(0, 150), (180, 210), (240, 270), (330, 360)]

    # Function to add non-overlap constraints for a person
    def add_busy_constraints(busy_intervals):
        for (b_start, b_end) in busy_intervals:
            s.add(Or(start + 60 <= b_start, start >= b_end))

    add_busy_constraints(anthony_busy)
    add_busy_constraints(pamela_busy)
    add_busy_constraints(zachary_busy)

    if s.check() == sat:
        m = s.model()
        start_min = m[start].as_long()

        # Calculate the hour and minute for the start time
        hours_start = start_min // 60
        minutes_start = start_min % 60
        start_hour = 9 + hours_start
        start_minute = minutes_start

        # Calculate end time
        end_min = start_min + 60
        hours_end = end_min // 60
        minutes_end = end_min % 60
        end_hour = 9 + hours_end
        end_minute = minutes_end

        # Format the time strings to have two digits for minutes
        start_str = f"{int(start_hour)}:{minutes_start:02d}"
        end_str = f"{int(end_hour)}:{minutes_end:02d}"

        # Print the solution
        print(f"Monday {start_str} to {end_str}")
    else:
        print("No solution found")

if __name__ == '__main__':
    main()