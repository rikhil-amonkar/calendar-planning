from z3 import *

def main():
    # Meeting duration in minutes
    duration = 30

    # Working hours on Monday: 9:00 (offset 0) to 17:00 (offset 480).
    # Meeting must finish by 17:00, so start + duration <= 480.
    start = Int('start')  # minutes offset from 9:00

    solver = Solver()
    solver.add(start >= 0, start + duration <= 480)

    # Michael's busy intervals (converted relative to 9:00)
    # Busy: 9:30-10:30 => [30, 90]
    solver.add(Or(start + duration <= 30, start >= 90))
    # Busy: 15:00-15:30 => [360, 390]
    solver.add(Or(start + duration <= 360, start >= 390))
    # Busy: 16:00-16:30 => [420, 450]
    solver.add(Or(start + duration <= 420, start >= 450))

    # Arthur's busy intervals (converted relative to 9:00)
    # Busy: 9:00-12:00 => [0, 180]
    solver.add(Or(start + duration <= 0, start >= 180))
    # Busy: 13:00-15:00 => [240, 360]
    solver.add(Or(start + duration <= 240, start >= 360))
    # Busy: 15:30-16:00 => [390, 420]
    solver.add(Or(start + duration <= 390, start >= 420))
    # Busy: 16:30-17:00 => [450, 480]
    solver.add(Or(start + duration <= 450, start >= 480))

    if solver.check() == sat:
        model = solver.model()
        meeting_start_offset = model.evaluate(start).as_long()  # minutes past 9:00
        # Convert offset into absolute time (minutes since midnight)
        meeting_start_total = 9 * 60 + meeting_start_offset
        meeting_end_total = meeting_start_total + duration

        # Convert minutes to HH:MM format
        start_hour = meeting_start_total // 60
        start_min = meeting_start_total % 60
        end_hour = meeting_end_total // 60
        end_min = meeting_end_total % 60

        start_time = f"{start_hour:02d}:{start_min:02d}"
        end_time = f"{end_hour:02d}:{end_min:02d}"

        # Output the day of the week and the meeting time range
        print("Monday")
        print("{" + start_time + ":" + end_time + "}")
    else:
        print("No feasible meeting time found.")

if __name__ == "__main__":
    main()