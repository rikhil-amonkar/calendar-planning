from z3 import Solver, Int, Or, And

def main():
    s = Solver()
    start = Int('start')

    # Work hours: 9:00 (0 min) to 17:00 (480 min)
    # Meeting duration: 60 min -> start must be between 0 and 420 inclusive
    s.add(start >= 0)
    s.add(start <= 420)

    # Kayla's blocked intervals (in minutes from 9:00)
    kayla_blocks = [(60, 90), (330, 420)]
    for block in kayla_blocks:
        a, b = block
        s.add(Or(start + 60 <= a, start >= b))

    # Rebecca's blocked intervals
    rebecca_blocks = [(0, 240), (270, 360), (390, 420)]
    for block in rebecca_blocks:
        a, b = block
        s.add(Or(start + 60 <= a, start >= b))

    if s.check() == 'sat':
        model = s.model()
        start_minutes = model[start].as_long()
        # Convert start_minutes to time string
        total_minutes = start_minutes
        hours = 9 + total_minutes // 60
        minutes = total_minutes % 60
        start_time = f"{hours:02d}:{minutes:02d}"
        # Calculate end time (start + 60 minutes)
        end_minutes = total_minutes + 60
        end_hours = 9 + end_minutes // 60
        end_minutes = end_minutes % 60
        end_time = f"{end_hours:02d}:{end_minutes:02d}"
        print(f"Monday {start_time} to {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()