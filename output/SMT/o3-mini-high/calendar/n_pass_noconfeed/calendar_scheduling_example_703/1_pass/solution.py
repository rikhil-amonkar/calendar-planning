from z3 import *

def main():
    # Create solver instance
    s = Solver()

    # Define meeting day variable:
    # 0 -> Monday, 1 -> Tuesday, 2 -> Wednesday
    day = Int('day')
    s.add(Or(day == 0, day == 1, day == 2))

    # Define meeting start time (in minutes after 9:00). Meeting duration is 60 minutes.
    t = Int('t')
    meeting_duration = 60
    s.add(t >= 0, t + meeting_duration <= 480)  # within work hours 9:00 (0) to 17:00 (480)

    # Add preference: Stephanie would like to avoid Monday (day 0).
    s.add(day != 0)

    # Betty cannot meet on Tuesday after 12:30.
    # For Tuesday (day == 1), the meeting must end by 12:30 (which is 210 minutes after 9:00).
    s.add(Implies(day == 1, t + meeting_duration <= 210))

    # Helper: For a given busy interval, if the meeting is on that day then it must not overlap the busy time.
    # Non-overlap: meeting_end <= busy_start or meeting_start >= busy_end.
    def add_busy_constraint(busy_day, busy_start, busy_end):
        s.add(Implies(day == busy_day, Or(t + meeting_duration <= busy_start, t >= busy_end)))

    # Schedules for Stephanie (times converted to minutes after 9:00):
    # Monday (day 0): 9:30-10:00 [30,60], 10:30-11:00 [90,120], 11:30-12:00 [150,180], 14:00-14:30 [300,330]
    add_busy_constraint(0, 30, 60)
    add_busy_constraint(0, 90, 120)
    add_busy_constraint(0, 150, 180)
    add_busy_constraint(0, 300, 330)
    # Tuesday (day 1): 12:00-13:00 [180,240]
    add_busy_constraint(1, 180, 240)
    # Wednesday (day 2): 9:00-10:00 [0,60], 13:00-14:00 [240,300]
    add_busy_constraint(2, 0, 60)
    add_busy_constraint(2, 240, 300)

    # Schedules for Betty:
    # Monday (day 0): 9:00-10:00 [0,60], 11:00-11:30 [120,150], 14:30-15:00 [330,360], 15:30-16:00 [390,420]
    add_busy_constraint(0, 0, 60)
    add_busy_constraint(0, 120, 150)
    add_busy_constraint(0, 330, 360)
    add_busy_constraint(0, 390, 420)
    # Tuesday (day 1): 9:00-9:30 [0,30], 11:30-12:00 [150,180], 12:30-14:30 [210,330], 15:30-16:00 [390,420]
    add_busy_constraint(1, 0, 30)
    add_busy_constraint(1, 150, 180)
    add_busy_constraint(1, 210, 330)
    add_busy_constraint(1, 390, 420)
    # Wednesday (day 2): 10:00-11:30 [60,150], 12:00-14:00 [180,300], 14:30-17:00 [330,480]
    add_busy_constraint(2, 60, 150)
    add_busy_constraint(2, 180, 300)
    add_busy_constraint(2, 330, 480)

    # Try solving the constraints
    if s.check() == sat:
        m = s.model()
        chosen_day = m[day].as_long()
        chosen_t = m[t].as_long()

        # Map integer day to day name
        day_map = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}
        day_str = day_map.get(chosen_day, "Unknown")

        # Compute start and end times
        start_minutes = chosen_t         # minutes after 9:00
        end_minutes = chosen_t + meeting_duration
        start_hour = 9 + start_minutes // 60
        start_min = start_minutes % 60
        end_hour = 9 + end_minutes // 60
        end_min = end_minutes % 60
        
        # Format as HH:MM:HH:MM (e.g., "10:00:11:00")
        time_str = f"{start_hour:02d}:{start_min:02d}:{end_hour:02d}:{end_min:02d}"
        print(f"Day: {day_str}, Time: {time_str}")
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()