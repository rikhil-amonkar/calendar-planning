from z3 import Solver, Int, Or

def minutes(hour, minute):
    return hour * 60 + minute

def main():
    solver = Solver()

    # Define integer variables:
    # d: 0 = Monday, 1 = Tuesday, 2 = Wednesday, 3 = Thursday
    # s: meeting start time in minutes from midnight.
    d = Int("d")
    s = Int("s")
    meeting_duration = 60
    meeting_end = s + meeting_duration

    # Domain constraints:
    solver.add(d >= 0, d <= 3)
    # Philip cannot meet on Wednesday:
    solver.add(d != 2)
    # Working hours: meeting must be within 09:00 to 17:00.
    solver.add(s >= minutes(9, 0), meeting_end <= minutes(17, 0))

    # Busy schedules (times in minutes from midnight).
    # Mapping: 0 = Monday, 1 = Tuesday, 2 = Wednesday, 3 = Thursday.
    busy = {
        "Laura": {
            0: [(minutes(10,30), minutes(11,0)),
                (minutes(12,30), minutes(13,0)),
                (minutes(14,30), minutes(15,30)),
                (minutes(16,0), minutes(17,0))],
            1: [(minutes(9,30), minutes(10,0)),
                (minutes(11,0), minutes(11,30)),
                (minutes(13,0), minutes(13,30)),
                (minutes(14,30), minutes(15,0)),
                (minutes(16,0), minutes(17,0))],
            2: [(minutes(11,30), minutes(12,0)),
                (minutes(12,30), minutes(13,0)),
                (minutes(15,30), minutes(16,30))],
            3: [(minutes(10,30), minutes(11,0)),
                (minutes(12,0), minutes(13,30)),
                (minutes(15,0), minutes(15,30)),
                (minutes(16,0), minutes(16,30))]
        },
        "Philip": {
            0: [(minutes(9,0), minutes(17,0))],
            1: [(minutes(9,0), minutes(11,0)),
                (minutes(11,30), minutes(12,0)),
                (minutes(13,0), minutes(13,30)),
                (minutes(14,0), minutes(14,30)),
                (minutes(15,0), minutes(16,30))],
            2: [(minutes(9,0), minutes(10,0)),
                (minutes(11,0), minutes(12,0)),
                (minutes(12,30), minutes(16,0)),
                (minutes(16,30), minutes(17,0))],
            3: [(minutes(9,0), minutes(10,30)),
                (minutes(11,0), minutes(12,30)),
                (minutes(13,0), minutes(17,0))]
        }
    }

    # For each busy interval, if the meeting is on that day then the meeting must not overlap with that busy period.
    for person in busy:
        for day_val, intervals in busy[person].items():
            for (bstart, bend) in intervals:
                solver.add(Or(d != day_val, meeting_end <= bstart, s >= bend))

    if solver.check() == 'sat' or solver.check() == True:
        model = solver.model()
        day_val = model[d].as_long()
        start_val = model[s].as_long()
        end_val = start_val + meeting_duration

        # Map numeric day to day name.
        day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}
        meeting_day = day_names[day_val]

        # Format times as HH:MM.
        def format_time(t):
            h = t // 60
            m = t % 60
            return f"{h:02d}:{m:02d}"
        
        start_time_str = format_time(start_val)
        end_time_str = format_time(end_val)

        # Output the solution in the specified format.
        print("SOLUTION:")
        print(f"Day: {meeting_day}")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()