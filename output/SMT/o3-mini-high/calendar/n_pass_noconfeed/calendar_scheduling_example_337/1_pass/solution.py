from z3 import Solver, Int, Or, sat

def main():
    # Create the SMT solver instance
    solver = Solver()

    # Meeting duration: 30 minutes
    duration = 30

    # Define the meeting start time (in minutes since midnight)
    # Work hours are 9:00 (540 minutes) to 17:00 (1020 minutes), so the latest start
    # is 17:00 - duration = 990 minutes.
    start = Int('start')
    solver.add(start >= 540, start <= 990)

    # Helper function for adding no-overlap constraint
    # For a meeting interval [a, b), our meeting [start, start+duration)
    # must either end before a, or start after b.
    def no_overlap(a, b):
        return Or(start + duration <= a, start >= b)

    # John's meetings (in minutes)
    # Meeting 1: 11:30 (690) to 12:00 (720)
    solver.add(no_overlap(690, 720))
    # Meeting 2: 14:00 (840) to 14:30 (870)
    solver.add(no_overlap(840, 870))

    # Megan's meetings
    # Meeting 1: 12:00 (720) to 12:30 (750)
    solver.add(no_overlap(720, 750))
    # Meeting 2: 14:00 (840) to 15:00 (900)
    solver.add(no_overlap(840, 900))
    # Meeting 3: 15:30 (930) to 16:00 (960)
    solver.add(no_overlap(930, 960))

    # Brandon has no meetings

    # Kimberly's meetings
    # Meeting 1: 9:00 (540) to 9:30 (570)
    solver.add(no_overlap(540, 570))
    # Meeting 2: 10:00 (600) to 10:30 (630)
    solver.add(no_overlap(600, 630))
    # Meeting 3: 11:00 (660) to 14:30 (870)
    solver.add(no_overlap(660, 870))
    # Meeting 4: 15:00 (900) to 16:00 (960)
    solver.add(no_overlap(900, 960))
    # Meeting 5: 16:30 (990) to 17:00 (1020)
    solver.add(no_overlap(990, 1020))

    # Sean's meetings
    # Meeting 1: 10:00 (600) to 11:00 (660)
    solver.add(no_overlap(600, 660))
    # Meeting 2: 11:30 (690) to 14:00 (840)
    solver.add(no_overlap(690, 840))
    # Meeting 3: 15:00 (900) to 15:30 (930)
    solver.add(no_overlap(900, 930))

    # Lori's meetings
    # Meeting 1: 9:00 (540) to 9:30 (570)
    solver.add(no_overlap(540, 570))
    # Meeting 2: 10:30 (630) to 12:00 (720)
    solver.add(no_overlap(630, 720))
    # Meeting 3: 13:00 (780) to 14:30 (870)
    solver.add(no_overlap(780, 870))
    # Meeting 4: 16:00 (960) to 16:30 (990)
    solver.add(no_overlap(960, 990))

    # Check overall constraints
    if solver.check() == sat:
        model = solver.model()
        meeting_start = model[start].as_long()
        meeting_end = meeting_start + duration

        # Function to convert minutes into HH:MM format
        def format_time(minutes):
            hh = minutes // 60
            mm = minutes % 60
            return f"{hh:02d}:{mm:02d}"

        start_str = format_time(meeting_start)
        end_str = format_time(meeting_end)

        # Output the meeting time range and day of the week
        print(f"Monday, {{{start_str}:{end_str}}}")
    else:
        print("No possible meeting time found.")

if __name__ == "__main__":
    main()