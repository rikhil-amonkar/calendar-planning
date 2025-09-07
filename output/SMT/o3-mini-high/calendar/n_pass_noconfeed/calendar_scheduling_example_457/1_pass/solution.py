from z3 import *

def main():
    duration = 30  # meeting duration in minutes
    start = Int("start")  # meeting start time in minutes after midnight
    solver = Solver()

    # Working hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
    solver.add(start >= 9 * 60)
    solver.add(start + duration <= 17 * 60)

    # Helper function: meeting [start, start+duration] must not overlap a busy interval [busy_start, busy_end]
    def no_overlap(busy_start, busy_end):
        return Or(start + duration <= busy_start, start >= busy_end)

    # Andrea is busy from 9:30 to 10:30 and from 13:30 to 14:30
    solver.add(no_overlap(9 * 60 + 30, 10 * 60 + 30))   # [570, 630]
    solver.add(no_overlap(13 * 60 + 30, 14 * 60 + 30))   # [810, 870]

    # Ruth is busy from 12:30 to 13:00 and from 15:00 to 15:30
    solver.add(no_overlap(12 * 60 + 30, 13 * 60))   # [750, 780]
    solver.add(no_overlap(15 * 60, 15 * 60 + 30))     # [900, 930]

    # Steven is busy from 10:00 to 10:30, 11:00 to 11:30, 12:00 to 12:30, 13:30 to 14:00, and 15:00 to 16:00
    solver.add(no_overlap(10 * 60, 10 * 60 + 30))   # [600, 630]
    solver.add(no_overlap(11 * 60, 11 * 60 + 30))   # [660, 690]
    solver.add(no_overlap(12 * 60, 12 * 60 + 30))   # [720, 750]
    solver.add(no_overlap(13 * 60 + 30, 14 * 60))   # [810, 840]
    solver.add(no_overlap(15 * 60, 16 * 60))         # [900, 960]

    # Kyle is busy from 9:00 to 9:30, 10:30 to 12:00, 12:30 to 13:00, 13:30 to 15:00, 15:30 to 16:00, 16:30 to 17:00
    solver.add(no_overlap(9 * 60, 9 * 60 + 30))           # [540, 570]
    solver.add(no_overlap(10 * 60 + 30, 12 * 60))         # [630, 720]
    solver.add(no_overlap(12 * 60 + 30, 13 * 60))         # [750, 780]
    solver.add(no_overlap(13 * 60 + 30, 15 * 60))         # [810, 900]
    solver.add(no_overlap(15 * 60 + 30, 16 * 60))         # [930, 960]
    solver.add(no_overlap(16 * 60 + 30, 17 * 60))         # [990, 1020]

    # Elijah is busy from 9:00 to 11:00, 11:30 to 13:00, 13:30 to 14:00, 15:30 to 16:00, and 16:30 to 17:00
    solver.add(no_overlap(9 * 60, 11 * 60))               # [540, 660]
    solver.add(no_overlap(11 * 60 + 30, 13 * 60))         # [690, 780]
    solver.add(no_overlap(13 * 60 + 30, 14 * 60))         # [810, 840]
    solver.add(no_overlap(15 * 60 + 30, 16 * 60))         # [930, 960]
    solver.add(no_overlap(16 * 60 + 30, 17 * 60))         # [990, 1020]

    # Lori is busy from 9:00 to 9:30, 10:00 to 11:30, 12:00 to 13:30, 14:00 to 16:00, and 16:30 to 17:00
    solver.add(no_overlap(9 * 60, 9 * 60 + 30))           # [540, 570]
    solver.add(no_overlap(10 * 60, 11 * 60 + 30))         # [600, 690]
    solver.add(no_overlap(12 * 60, 13 * 60 + 30))         # [720, 810]
    solver.add(no_overlap(14 * 60, 16 * 60))              # [840, 960]
    solver.add(no_overlap(16 * 60 + 30, 17 * 60))         # [990, 1020]

    if solver.check() == sat:
        model = solver.model()
        meeting_start = model[start].as_long()
        meeting_end = meeting_start + duration

        # Convert meeting times from minutes to HH:MM format.
        start_hour = meeting_start // 60
        start_min = meeting_start % 60
        end_hour = meeting_end // 60
        end_min = meeting_end % 60

        # Format the time as HH:MM:HH:MM
        time_range = f"{start_hour:02d}:{start_min:02d}:{end_hour:02d}:{end_min:02d}"
        day = "Monday"
        print(day, time_range)
    else:
        print("No valid meeting time found.")

if __name__ == "__main__":
    main()