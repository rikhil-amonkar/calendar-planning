from z3 import *

def main():
    # Input data for requirements: start times, end times, and minimal durations
    req_start = [0, 5]
    req_end = [10, 10]
    reqs = [5, 3]  # minimal durations for requirements A and B
    max_time = 10   # maximum time in the schedule

    # Activity variables: two activities with start and end times
    start0 = Int('start0')
    end0 = Int('end0')
    start1 = Int('start1')
    end1 = Int('end1')
    start = [start0, start1]
    end = [end0, end1]

    # Assignment: each requirement (A and B) is assigned to an activity (0 or 1)
    assign0 = Int('assign0')  # for requirement A
    assign1 = Int('assign1')  # for requirement B
    assign = [assign0, assign1]

    s = Solver()

    # Domains for assignment variables: 0 or 1
    s.add(assign0 >= 0, assign0 <= 1)
    s.add(assign1 >= 0, assign1 <= 1)

    # Conditions for activity assignments
    A0 = (assign0 == 0)  # requirement A in activity0
    B0 = (assign1 == 0)  # requirement B in activity0
    A1 = (assign0 == 1)  # requirement A in activity1
    B1 = (assign1 == 1)  # requirement B in activity1

    # Constraints for activity0
    s.add(start0 >= If(A0, req_start[0], 0))
    s.add(start0 >= If(B0, req_start[1], 0))
    s.add(end0 <= If(A0, req_end[0], max_time))
    s.add(end0 <= If(B0, req_end[1], max_time))
    min_dur0 = If(And(A0, B0), Max(reqs[0], reqs[1]),
                 If(A0, reqs[0],
                 If(B0, reqs[1], 0)))
    s.add(end0 - start0 >= min_dur0)

    # Constraints for activity1
    s.add(start1 >= If(A1, req_start[0], 0))
    s.add(start1 >= If(B1, req_start[1], 0))
    s.add(end1 <= If(A1, req_end[0], max_time))
    s.add(end1 <= If(B1, req_end[1], max_time))
    min_dur1 = If(And(A1, B1), Max(reqs[0], reqs[1]),
                 If(A1, reqs[0],
                 If(B1, reqs[1], 0)))
    s.add(end1 - start1 >= min_dur1)

    # Activities must not overlap
    s.add(Or(end0 <= start1, end1 <= start0))

    # Non-negative start times and end times <= max_time
    s.add(start0 >= 0, start0 <= max_time)
    s.add(start1 >= 0, start1 <= max_time)
    s.add(end0 >= 0, end0 <= max_time)
    s.add(end1 >= 0, end1 <= max_time)

    # Check and get the solution
    if s.check() == sat:
        m = s.model()
        a0 = m.evaluate(assign0).as_long()
        a1 = m.evaluate(assign1).as_long()
        s0 = m.evaluate(start0)
        e0 = m.evaluate(end0)
        s1 = m.evaluate(start1)
        e1 = m.evaluate(end1)

        # Start and end times for requirement A (based on its assignment)
        start_A = If(a0 == 0, s0, s1)
        end_A = If(a0 == 0, e0, e1)
        start_A_val = m.evaluate(start_A)
        end_A_val = m.evaluate(end_A)

        # Start and end times for requirement B (based on its assignment)
        start_B = If(a1 == 0, s0, s1)
        end_B = If(a1 == 0, e0, e1)
        start_B_val = m.evaluate(start_B)
        end_B_val = m.evaluate(end_B)

        print("Solution found:")
        print(f"Requirement A is assigned to activity {a0}: start={start_A_val}, end={end_A_val}")
        print(f"Requirement B is assigned to activity {a1}: start={start_B_val}, end={end_B_val}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()