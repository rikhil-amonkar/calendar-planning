from z3 import *

def main():
    solver = Solver()
    start = Int('start')
    end = start + 60  # 1 hour meeting

    # Work hours: 9:00 (540) to 17:00 (1020)
    solver.add(start >= 540)
    solver.add(end <= 1020)

    # Busy periods in minutes since midnight
    # Stephanie: 10:00-10:30 (600-630), 16:00-16:30 (960-1020)
    for b_start, b_end in [(600, 630), (960, 1020)]:
        solver.add(Or(end <= b_start, start >= b_end))
    
    # Cheryl: 10:00-10:30 (600-630), 11:30-12:00 (690-720), 13:30-14:00 (810-840), 16:30-17:00 (990-1020)
    for b_start, b_end in [(600, 630), (690, 720), (810, 840), (990, 1020)]:
        solver.add(Or(end <= b_start, start >= b_end))
    
    # Bradley: 9:30-10:00 (570-600), 10:30-11:30 (630-690), 13:30-14:00 (810-840), 14:30-15:00 (870-900), 15:30-17:00 (930-1020)
    for b_start, b_end in [(570, 600), (630, 690), (810, 840), (870, 900), (930, 1020)]:
        solver.add(Or(end <= b_start, start >= b_end))
    
    # Steven: 9:00-12:00 (540-720), 13:00-13:30 (780-810), 14:30-17:00 (870-1020)
    for b_start, b_end in [(540, 720), (780, 810), (870, 1020)]:
        solver.add(Or(end <= b_start, start >= b_end))

    if solver.check() == sat:
        model = solver.model()
        start_time = model[start].as_long()
        end_time = start_time + 60

        def to_time(minutes):
            hours = minutes // 60
            mins = minutes % 60
            return f"{hours:02d}:{mins:02d}"

        start_str = to_time(start_time)
        end_str = to_time(end_time)
        print(f"{{{start_str}:{end_str}}} Monday")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()