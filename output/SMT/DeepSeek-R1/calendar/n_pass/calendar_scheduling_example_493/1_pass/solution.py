from z3 import *

def main():
    s = Solver()
    start = Int('start')
    s.add(start >= 0)
    s.add(start <= 450)  # Meeting must end by 17:00 (480 minutes)

    # Busy intervals for each participant (in minutes from 9:00)
    stephanie_busy = [(120, 150), (330, 360)]
    joe_busy = [(0, 30), (60, 180), (210, 240), (300, 480)]
    diana_busy = [(0, 90), (150, 180), (240, 300), (330, 390), (420, 480)]
    deborah_busy = [(0, 60), (90, 180), (210, 240), (270, 300), (330, 390), (420, 450)]

    # Combine all participants' busy intervals
    all_busy = [stephanie_busy, joe_busy, diana_busy, deborah_busy]

    for participant in all_busy:
        for (a, b) in participant:
            s.add(Or(start + 30 <= a, start >= b))

    if s.check() == sat:
        m = s.model()
        start_min = m[start].as_long()
        hours = start_min // 60
        minutes = start_min % 60
        start_hour = 9 + hours
        start_time = f"{start_hour:02d}:{minutes:02d}"

        end_min = start_min + 30
        end_hours = end_min // 60
        end_minutes = end_min % 60
        end_time = f"{9 + end_hours:02d}:{end_minutes:02d}"

        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()