from z3 import *

def main():
    # Create variables for day and start time (in minutes since 9:00)
    day = Int('day')
    start_time = Int('start_time')  # 0 = 9:00, 480 = 17:00

    opt = Optimize()

    # Day constraints (0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday)
    opt.add(day >= 0, day <= 3)
    # Meeting must start within work hours and allow 30-minute duration
    opt.add(start_time >= 0, start_time + 30 <= 480)

    # James's meetings (start and end times in minutes since 9:00)
    james_meetings = {
        0: [(0, 30), (90, 120), (210, 240), (330, 390), (450, 480)],    # Monday
        1: [(0, 120), (150, 180), (210, 330), (420, 480)],              # Tuesday
        2: [(60, 120), (180, 240), (270, 420)],                         # Wednesday
        3: [(30, 150), (180, 210), (240, 270), (300, 330), (450, 480)]  # Thursday
    }

    # Add constraints for James's schedule
    for d in range(4):
        for (s, e) in james_meetings[d]:
            opt.add(Implies(day == d, 
                          Not(And(start_time < e, start_time + 30 > s))))

    # Define optimization target: minimize day*480 + start_time for earliest possible time
    total_time = day * 480 + start_time
    opt.minimize(total_time)

    if opt.check() == sat:
        model = opt.model()
        day_val = model[day].as_long()
        start_val = model[start_time].as_long()

        # Convert time to HH:MM format
        hours = 9 + (start_val // 60)
        minutes = start_val % 60
        start_str = f"{hours:02d}:{minutes:02d}"

        days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
        print(f"Schedule the meeting on {days[day_val]} at {start_str}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()