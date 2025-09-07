from z3 import *

def schedule_meeting():
    s = Solver()

    day = Int('day')
    start_time = Int('start_time')

    # Constraints for day and time
    s.add(And(day >= 0, day <= 3))  # Days: Monday (0) to Thursday (3)
    s.add(And(start_time >= 540, start_time <= 990))  # 9:00 to 16:30 in minutes

    # Ruth is only available on Thursday
    s.add(day == 3)

    # Julie avoids Thursday before 11:30 (690 minutes)
    # Available slot on Thursday is 14:30 (870) to 15:00 (900)
    s.add(And(start_time >= 870, start_time + 30 <= 900))

    if s.check() == sat:
        m = s.model()
        day_val = m[day].as_long()
        start_val = m[start_time].as_long()
        
        # Convert to time format
        start_hr = start_val // 60
        start_min = start_val % 60
        end_val = start_val + 30
        end_hr = end_val // 60
        end_min = end_val % 60
        
        days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
        day_name = days[day_val]
        print(f"{day_name} {start_hr:02d}:{start_min:02d}:{end_hr:02d}:{end_min:02d}")
    else:
        print("No solution")

schedule_meeting()