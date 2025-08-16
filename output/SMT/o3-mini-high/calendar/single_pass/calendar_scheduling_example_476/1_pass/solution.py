from z3 import *

def main():
    solver = Solver()
    
    # We represent the meeting start time as an integer number of minutes after 9:00.
    # The meeting must last 30 minutes, and overall must finish by 17:00 (i.e. 480 minutes after 9:00).
    meeting_start = Int('meeting_start')
    duration = 30
    # Working hours constraint: meeting_start must be between 0 and 450 (so that meeting_start + 30 <= 480).
    solver.add(meeting_start >= 0, meeting_start + duration <= 480)
    
    # Roger's preference: he would rather not meet before 12:30.
    # 12:30 is 210 minutes after 9:00.
    solver.add(meeting_start >= 210)
    
    # Helper function: given a busy interval [busy_start, busy_end),
    # the meeting [meeting_start, meeting_start+duration) must NOT overlap it.
    # Two intervals do not overlap if either the meeting ends no later than busy_start
    # or the meeting starts no earlier than busy_end.
    def no_overlap(busy_start, busy_end):
        return Or(meeting_start + duration <= busy_start, meeting_start >= busy_end)
    
    # Add constraints for each participant’s busy times.
    # Times are converted to minutes after 9:00:
    # 9:00  -> 0
    # 9:30  -> 30
    # 10:00 -> 60
    # 10:30 -> 90
    # 11:30 -> 150
    # 12:00 -> 180
    # 12:30 -> 210
    # 13:00 -> 240
    # 13:30 -> 270
    # 14:00 -> 300
    # 14:30 -> 330
    # 15:30 -> 390
    # 16:00 -> 420
    # 16:30 -> 450
    # 17:00 -> 480
    
    # Kathleen is busy 14:30 to 15:30  -> [330, 390]
    solver.add(no_overlap(330, 390))
    
    # Carolyn is busy 12:00 to 12:30  -> [180, 210] and 13:00 to 13:30 -> [240, 270]
    solver.add(no_overlap(180, 210))
    solver.add(no_overlap(240, 270))
    
    # Cheryl is busy 9:00-9:30  -> [0, 30], 10:00-11:30 -> [60, 150],
    # 12:30-13:30 -> [210, 270], and 14:00-17:00 -> [300, 480]
    solver.add(no_overlap(0, 30))
    solver.add(no_overlap(60, 150))
    solver.add(no_overlap(210, 270))
    solver.add(no_overlap(300, 480))
    
    # Virginia is busy 9:30-11:30 -> [30, 150], 12:00-12:30 -> [180, 210],
    # 13:00-13:30 -> [240, 270], 14:30-15:30 -> [330, 390], and 16:00-17:00 -> [420, 480]
    solver.add(no_overlap(30, 150))
    solver.add(no_overlap(180, 210))
    solver.add(no_overlap(240, 270))
    solver.add(no_overlap(330, 390))
    solver.add(no_overlap(420, 480))
    
    # Angela is busy 9:30-10:00 -> [30, 60], 10:30-11:30 -> [90, 150],
    # 12:00-12:30 -> [180, 210], 13:00-13:30 -> [240, 270],
    # and 14:00-16:30 -> [300, 450]
    solver.add(no_overlap(30, 60))
    solver.add(no_overlap(90, 150))
    solver.add(no_overlap(180, 210))
    solver.add(no_overlap(240, 270))
    solver.add(no_overlap(300, 450))
    
    # Daniel has no meetings, so no extra constraints are needed.

    # Solve the constraints.
    if solver.check() == sat:
        model = solver.model()
        # meeting_start is the number of minutes after 9:00.
        start_val = model[meeting_start].as_long()
        
        # Compute the actual start and end times.
        base = 9 * 60  # 9:00 in minutes after midnight.
        actual_start = base + start_val
        actual_end = base + start_val + duration
        
        def format_time(total_minutes):
            hour = total_minutes // 60
            minute = total_minutes % 60
            return f"{hour:02d}:{minute:02d}"
        
        day = "Monday"
        start_time_str = format_time(actual_start)
        end_time_str = format_time(actual_end)
        
        # Print the solution in the required format.
        print("SOLUTION:")
        print(f"Day: {day}")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()