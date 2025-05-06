from z3 import *

def main():
    # Create variables for day and start time (in minutes since 9:00)
    day = Int('day')
    start_time = Int('start_time')  # 0 = 9:00, 480 = 17:00

    opt = Optimize()

    # Day constraints (0=Monday, 1=Tuesday, 2=Wednesday)
    opt.add(day >= 0, day <= 2)
    # Meeting must start within work hours and allow 30-minute duration
    opt.add(start_time >= 0, start_time + 30 <= 480)

    # Samuel's meetings (start and end times in minutes since 9:00)
    samuel_meetings = {
        0: [(90, 120), (180, 210), (240, 360), (390, 450)],   # Monday
        1: [(0, 180), (300, 390), (450, 480)],                 # Tuesday
        2: [(90, 120), (150, 180), (210, 240), (300, 330), (360, 420)]  # Wednesday
    }

    # Add constraints for Samuel's schedule
    for d in samuel_meetings:
        for (s, e) in samuel_meetings[d]:
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

        days = ["Monday", "Tuesday", "Wednesday"]
        print(f"Schedule the meeting on {days[day_val]} at {start_str}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()