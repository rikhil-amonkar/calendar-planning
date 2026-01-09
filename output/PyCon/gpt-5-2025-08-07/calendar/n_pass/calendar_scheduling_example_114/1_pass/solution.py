# Requires: python-constraint
from constraint import Problem

def t(h, m=0):
    return h * 60 + m

def mm_to_str(mm):
    h = mm // 60
    m = mm % 60
    return f"{h:02d}:{m:02d}"

def intervals_overlap(a_start, a_end, b_start, b_end):
    # Treat intervals as [start, end); overlap if they intersect with non-zero length
    return not (a_end <= b_start or a_start >= b_end)

def build_problem():
    meeting_day = "Monday"
    work_start = t(9, 0)
    work_end = t(17, 0)
    meeting_duration = 60  # minutes

    # Busy schedules (start, end) in minutes from midnight
    schedules = {
        "Stephanie": [(t(10, 0), t(10, 30)), (t(16, 0), t(16, 30))],
        "Cheryl":    [(t(10, 0), t(10, 30)), (t(11, 30), t(12, 0)),
                      (t(13, 30), t(14, 0)), (t(16, 30), t(17, 0))],
        "Bradley":   [(t(9, 30), t(10, 0)), (t(10, 30), t(11, 30)),
                      (t(13, 30), t(14, 0)), (t(14, 30), t(15, 0)),
                      (t(15, 30), t(17, 0))],
        "Steven":    [(t(9, 0), t(12, 0)), (t(13, 0), t(13, 30)),
                      (t(14, 30), t(17, 0))],
    }

    # Candidate start times at 30-minute increments within work hours
    domain_starts = list(range(work_start, work_end - meeting_duration + 1, 30))

    def slot_is_free(start):
        end = start + meeting_duration
        # Must remain within work hours
        if start < work_start or end > work_end:
            return False
        # Check each participant's busy intervals
        for busy_list in schedules.values():
            for b_start, b_end in busy_list:
                if intervals_overlap(start, end, b_start, b_end):
                    return False
        return True

    problem = Problem()
    problem.addVariable("start", domain_starts)
    problem.addConstraint(lambda s: slot_is_free(s), ("start",))
    return problem, meeting_day, meeting_duration

def main():
    problem, meeting_day, meeting_duration = build_problem()
    solutions = problem.getSolutions()
    if not solutions:
        print(meeting_day)
        print("{NoSolution}")
        return

    # Choose the earliest valid start time
    best = min(solutions, key=lambda sol: sol["start"])
    start = best["start"]
    end = start + meeting_duration

    start_str = mm_to_str(start)
    end_str = mm_to_str(end)

    print(meeting_day)
    print(f"{{{start_str}:{end_str}}}")

if __name__ == "__main__":
    main()