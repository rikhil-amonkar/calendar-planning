# Requires: python-constraint (pip install python-constraint)
from constraint import Problem

def time_to_str(m):
    return f"{m//60:02d}:{m%60:02d}"

def no_overlap(day, start, end, blocks_by_day):
    for (bstart, bend) in blocks_by_day.get(day, []):
        # Overlap if start < bend and end > bstart
        if start < bend and end > bstart:
            return False
    return True

def main():
    days = ["Monday", "Tuesday", "Wednesday"]
    duration = 60  # minutes
    start_domain = list(range(9*60, 17*60 - duration + 1, 30))  # 09:00 to 16:00
    end_domain = [s + duration for s in start_domain]

    # Existing schedules (blocked intervals) in minutes from 00:00
    judith_blocks = {
        "Monday":    [(12*60, 12*60 + 30)],              # 12:00-12:30
        "Tuesday":   [],
        "Wednesday": [(11*60 + 30, 12*60)]               # 11:30-12:00
    }

    timothy_blocks = {
        "Monday": [
            (9*60 + 30, 10*60),       # 09:30-10:00
            (10*60 + 30, 11*60 + 30), # 10:30-11:30
            (12*60 + 30, 14*60),      # 12:30-14:00
            (15*60 + 30, 17*60)       # 15:30-17:00
        ],
        "Tuesday": [
            (9*60 + 30, 13*60),       # 09:30-13:00
            (13*60 + 30, 14*60),      # 13:30-14:00
            (14*60 + 30, 17*60)       # 14:30-17:00
        ],
        "Wednesday": [
            (9*60, 9*60 + 30),        # 09:00-09:30
            (10*60 + 30, 11*60),      # 10:30-11:00
            (13*60 + 30, 14*60 + 30), # 13:30-14:30
            (15*60, 15*60 + 30),      # 15:00-15:30
            (16*60, 16*60 + 30)       # 16:00-16:30
        ]
    }

    # Build the base problem (hard constraints)
    problem = Problem()
    problem.addVariable("Day", days)
    problem.addVariable("Start", start_domain)
    problem.addVariable("End", end_domain)

    # Link start and end by duration
    problem.addConstraint(lambda s, e: e - s == duration, ("Start", "End"))

    # Participants' availability constraints (no overlap with blocks)
    problem.addConstraint(
        lambda Day, Start, End, blocks=judith_blocks: no_overlap(Day, Start, End, blocks),
        ("Day", "Start", "End")
    )
    problem.addConstraint(
        lambda Day, Start, End, blocks=timothy_blocks: no_overlap(Day, Start, End, blocks),
        ("Day", "Start", "End")
    )

    solutions = problem.getSolutions()

    # Apply preferences:
    # - Judith would like to avoid Monday
    # - Judith would like to avoid Wednesday before 12:00
    def preference_score(sol):
        score = 0
        if sol["Day"] == "Monday":
            score += 100  # strong penalty
        if sol["Day"] == "Wednesday" and sol["Start"] < 12*60:
            score += 10   # moderate penalty
        return score

    # Choose solution with minimal preference penalty; tie-break by earliest start
    best = min(solutions, key=lambda s: (preference_score(s), s["Start"]))

    # Output: both the day and the time range in {HH:MM:HH:MM}
    print(best["Day"])
    print(f"{{{time_to_str(best['Start'])}:{time_to_str(best['End'])}}}")

if __name__ == "__main__":
    main()