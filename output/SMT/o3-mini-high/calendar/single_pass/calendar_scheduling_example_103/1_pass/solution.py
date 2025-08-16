from z3 import Solver, Int, Or

def main():
    # Convert times to minutes: 9:00 is 540, 17:00 is 1020.
    meeting_duration = 30  # minutes
    meeting_start = Int('meeting_start')
    meeting_end = meeting_start + meeting_duration

    solver = Solver()
    # The meeting must be within work hours.
    solver.add(meeting_start >= 540)
    solver.add(meeting_end <= 1020)

    # For any blocked interval [block_start, block_end),
    # the meeting must lie completely before or completely after.
    def add_block(block_start, block_end):
        solver.add(Or(meeting_end <= block_start, meeting_start >= block_end))

    # Diane's blocked intervals:
    # 9:30 to 10:00 -> (570,600) and 14:30 to 15:00 -> (870,900)
    add_block(570, 600)
    add_block(870, 900)

    # Jack's blocked intervals:
    # 13:30 to 14:00 -> (810,840) and 14:30 to 15:00 -> (870,900)
    add_block(810, 840)
    add_block(870, 900)

    # Eugene's blocked intervals:
    # 9:00 to 10:00 -> (540,600), 10:30 to 11:30 -> (630,690),
    # 12:00 to 14:30 -> (720,870), 15:00 to 16:30 -> (900,990)
    add_block(540, 600)
    add_block(630, 690)
    add_block(720, 870)
    add_block(900, 990)

    # Patricia's blocked intervals:
    # 9:30 to 10:30 -> (570,630), 11:00 to 12:00 -> (660,720),
    # 12:30 to 14:00 -> (750,840), 15:00 to 16:30 -> (900,990)
    add_block(570, 630)
    add_block(660, 720)
    add_block(750, 840)
    add_block(900, 990)

    if solver.check() == 'sat':
        model = solver.model()
        start_val = model[meeting_start].as_long()
        end_val = start_val + meeting_duration
        
        # Convert minutes back to HH:MM format.
        start_hour = start_val // 60
        start_min = start_val % 60
        end_hour = end_val // 60
        end_min = end_val % 60
        start_time_str = f"{start_hour:02d}:{start_min:02d}"
        end_time_str = f"{end_hour:02d}:{end_min:02d}"
        
        print("SOLUTION:")
        print("Day: Monday")
        print("Start Time: " + start_time_str)
        print("End Time: " + end_time_str)
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()