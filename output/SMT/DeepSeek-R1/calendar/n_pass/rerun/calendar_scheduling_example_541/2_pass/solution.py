from z3 import Solver, Int, Or

def main():
    s = Solver()
    start = Int('start')

    # Work hours: 9:00 (0 min) to 17:00 (480 min)
    # Meeting duration: 60 min -> start between 0 and 420 inclusive
    s.add(start >= 0)
    s.add(start <= 420)

    # Kayla's blocked intervals (minutes from 9:00)
    kayla_blocks = [(60, 90), (330, 420)]
    for a, b in kayla_blocks:
        s.add(Or(start + 60 <= a, start >= b))

    # Rebecca's blocked intervals
    rebecca_blocks = [(0, 240), (270, 360), (390, 420)]
    for a, b in rebecca_blocks:
        s.add(Or(start + 60 <= a, start >= b))

    if s.check() == 'sat':
        model = s.model()
        start_min = model[start].as_long()
        # Convert to time string
        start_hr = 9 + start_min // 60
        start_min %= 60
        end_min_val = start_min + 60
        end_hr = 9 + (start_min + 60) // 60
        end_min_val %= 60
        
        print(f"Monday {start_hr:02d}:{start_min:02d} to {end_hr:02d}:{end_min_val:02d}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()