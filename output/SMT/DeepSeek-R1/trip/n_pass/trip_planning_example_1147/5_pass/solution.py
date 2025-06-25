from z3 import *

def main():
    # Requirement time windows for 22-day itinerary
    req_start = [0, 0]   # Both requirements can start at day 0
    req_end = [22, 22]   # Both requirements can end at day 22
    reqs = [5, 3]        # Minimal durations
    max_time = 22        # Maximum schedule time

    # Activity start/end variables
    start0 = Int('start0')
    end0 = Int('end0')
    start1 = Int('start1')
    end1 = Int('end1')

    # Activity assignment variables
    assign0 = Int('assign0')  # Requirement A assignment
    assign1 = Int('assign1')  # Requirement B assignment

    s = Solver()

    # Assignment domains (0 or 1)
    s.add(assign0 >= 0, assign0 <= 1)
    s.add(assign1 >= 0, assign1 <= 1)

    # Activity assignment conditions
    A0 = (assign0 == 0)  # A in activity0
    B0 = (assign1 == 0)  # B in activity0
    A1 = (assign0 == 1)  # A in activity1
    B1 = (assign1 == 1)  # B in activity1

    # Constraints for activity0
    s.add(start0 >= If(A0, req_start[0], 0))
    s.add(start0 >= If(B0, req_start[1], 0))
    s.add(end0 <= If(A0, req_end[0], max_time))
    s.add(end0 <= If(B0, req_end[1], max_time))
    min_dur0 = If(And(A0, B0), max(reqs[0], reqs[1]),
                 If(A0, reqs[0],
                 If(B0, reqs[1], 0)))
    s.add(end0 - start0 >= min_dur0)

    # Constraints for activity1
    s.add(start1 >= If(A1, req_start[0], 0))
    s.add(start1 >= If(B1, req_start[1], 0))
    s.add(end1 <= If(A1, req_end[0], max_time))
    s.add(end1 <= If(B1, req_end[1], max_time))
    min_dur1 = If(And(A1, B1), max(reqs[0], reqs[1]),
                 If(A1, reqs[0],
                 If(B1, reqs[1], 0)))
    s.add(end1 - start1 >= min_dur1)

    # Non-overlapping activities
    s.add(Or(end0 <= start1, end1 <= start0))

    # Time bounds
    s.add(start0 >= 0, start0 <= max_time)
    s.add(start1 >= 0, start1 <= max_time)
    s.add(end0 >= 0, end0 <= max_time)
    s.add(end1 >= 0, end1 <= max_time)

    # Overall trip duration constraint (22 days)
    overall_start = Int('overall_start')
    overall_end = Int('overall_end')
    s.add(overall_start == If(start0 <= start1, start0, start1))
    s.add(overall_end == If(end0 >= end1, end0, end1))
    s.add(overall_end - overall_start == 22)

    # Solve and output
    if s.check() == sat:
        m = s.model()
        a0 = m.evaluate(assign0).as_long()
        a1 = m.evaluate(assign1).as_long()
        s0 = m.evaluate(start0).as_long()
        e0 = m.evaluate(end0).as_long()
        s1 = m.evaluate(start1).as_long()
        e1 = m.evaluate(end1).as_long()

        # Requirement A times
        start_A = s0 if a0 == 0 else s1
        end_A = e0 if a0 == 0 else e1

        # Requirement B times
        start_B = s0 if a1 == 0 else s1
        end_B = e0 if a1 == 0 else e1

        # Overall start/end times
        os_val = min(s0, s1)
        oe_val = max(e0, e1)
        duration = oe_val - os_val

        print("Solution found:")
        print(f"Requirement A: activity {a0}, start={start_A}, end={end_A}")
        print(f"Requirement B: activity {a1}, start={start_B}, end={end_B}")
        print(f"Trip duration: {oe_val} - {os_val} = {duration} days")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()