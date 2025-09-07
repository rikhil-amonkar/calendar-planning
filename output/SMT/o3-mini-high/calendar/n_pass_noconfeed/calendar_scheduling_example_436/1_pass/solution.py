from z3 import *

def main():
    # Meeting requirements: 30-minute meeting on Monday between 9:00 and 17:00
    meeting_duration = 30
    day = "Monday"
    work_start = 9 * 60      # 540 minutes (9:00)
    work_end = 17 * 60       # 1020 minutes (17:00)

    # Define the meeting start time as an integer (minutes past midnight)
    start = Int('start')
    s = Solver()

    # Constraint: meeting must start and end within work hours
    s.add(start >= work_start, start + meeting_duration <= work_end)

    # Busy intervals for each participant (in minutes after midnight)
    busy_intervals = []
    
    # Patrick: 13:30-14:00, 14:30-15:00
    busy_intervals.append((13 * 60 + 30, 14 * 60))   # 810, 840
    busy_intervals.append((14 * 60 + 30, 15 * 60))     # 870, 900

    # Shirley: 9:00-9:30, 11:00-11:30, 12:00-12:30, 14:30-15:00, 16:00-17:00
    busy_intervals.append((9 * 60, 9 * 60 + 30))       # 540, 570
    busy_intervals.append((11 * 60, 11 * 60 + 30))     # 660, 690
    busy_intervals.append((12 * 60, 12 * 60 + 30))     # 720, 750
    busy_intervals.append((14 * 60 + 30, 15 * 60))     # 870, 900
    busy_intervals.append((16 * 60, 17 * 60))          # 960, 1020

    # Jeffrey: 9:00-9:30, 10:30-11:00, 11:30-12:00, 13:00-13:30, 16:00-17:00
    busy_intervals.append((9 * 60, 9 * 60 + 30))       # 540, 570
    busy_intervals.append((10 * 60 + 30, 11 * 60))     # 630, 660
    busy_intervals.append((11 * 60 + 30, 12 * 60))     # 690, 720
    busy_intervals.append((13 * 60, 13 * 60 + 30))     # 780, 810
    busy_intervals.append((16 * 60, 17 * 60))          # 960, 1020

    # Gloria: 11:30-12:00, 15:00-15:30
    busy_intervals.append((11 * 60 + 30, 12 * 60))     # 690, 720
    busy_intervals.append((15 * 60, 15 * 60 + 30))     # 900, 930

    # Nathan: 9:00-9:30, 10:30-12:00, 14:00-17:00
    busy_intervals.append((9 * 60, 9 * 60 + 30))       # 540, 570
    busy_intervals.append((10 * 60 + 30, 12 * 60))     # 630, 720
    busy_intervals.append((14 * 60, 17 * 60))          # 840, 1020

    # Angela: 9:00-9:30, 10:00-11:00, 12:30-15:00, 15:30-16:30
    busy_intervals.append((9 * 60, 9 * 60 + 30))       # 540, 570
    busy_intervals.append((10 * 60, 11 * 60))          # 600, 660
    busy_intervals.append((12 * 60 + 30, 15 * 60))     # 750, 900
    busy_intervals.append((15 * 60 + 30, 16 * 60 + 30))# 930, 990

    # David: 9:00-9:30, 10:00-10:30, 11:00-14:00, 14:30-16:30
    busy_intervals.append((9 * 60, 9 * 60 + 30))       # 540, 570
    busy_intervals.append((10 * 60, 10 * 60 + 30))     # 600, 630
    busy_intervals.append((11 * 60, 14 * 60))          # 660, 840
    busy_intervals.append((14 * 60 + 30, 16 * 60 + 30))# 870, 990

    # For every busy interval, ensure the meeting does not overlap
    # The meeting [start, start+30] must either end before a busy interval starts
    # or start after a busy interval ends.
    for (busy_start, busy_end) in busy_intervals:
        s.add(Or(start + meeting_duration <= busy_start, start >= busy_end))
    
    # Check for a valid meeting time
    if s.check() == sat:
        model = s.model()
        meeting_start = model[start].as_long()
        meeting_end = meeting_start + meeting_duration

        # Convert minutes to HH:MM format
        start_hour = meeting_start // 60
        start_minute = meeting_start % 60
        end_hour = meeting_end // 60
        end_minute = meeting_end % 60

        # Format the time as HH:MM:HH:MM (e.g., "09:30:10:00")
        time_range = "{:02d}:{:02d}:{:02d}:{:02d}".format(start_hour, start_minute, end_hour, end_minute)
        print(day, time_range)
    else:
        print("No valid meeting time found.")

if __name__ == "__main__":
    main()