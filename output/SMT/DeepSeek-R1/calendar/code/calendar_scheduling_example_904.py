from z3 import *

def main():
    s = Solver()
    S = Int('S')  # Start time in minutes since midnight

    # Day is constrained to Tuesday (only valid day after applying preferences)
    s.add(S >= 720)   # 12:00 (Tuesday start after Bradley's constraint)
    s.add(S + 30 <= 1020)  # 17:00 end

    # Convert all schedules to Tuesday constraints
    daniel_busy = [(780, 810), (930, 960), (990, 1020)]  # 13:00-13:30, 15:30-16:00, 16:30-17:00
    bradley_busy = [(720, 780), (810, 840), (930, 990)]  # 12:00-13:00, 13:30-14:00, 15:30-16:30

    # Combine all busy intervals
    all_busy = daniel_busy + bradley_busy

    # Ensure meeting doesn't overlap with any busy time
    for start, end in all_busy:
        s.add(Or(S + 30 <= start, S >= end))

    if s.check() == sat:
        model = s.model()
        start_time = model[S].as_long()
        h = start_time // 60
        m = start_time % 60
        print(f"Tuesday {h:02d}:{m:02d} to {(start_time + 30) // 60:02d}:{(start_time + 30) % 60:02d}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()