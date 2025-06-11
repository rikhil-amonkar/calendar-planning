from z3 import *

def main():
    # Define the integer variables
    day = Int('day')
    start = Int('start')  # in minutes

    s = Solver()

    # Day must be 0 (Monday), 1 (Tuesday), or 2 (Wednesday)
    s.add(Or(day == 0, day == 1, day == 2))
    
    # Work hours: 9:00 to 17:00 (540 to 1020 minutes)
    s.add(start >= 540)
    s.add(start + 30 <= 1020)
    
    # Joyce's preference: avoid Monday before 12:00 (720 minutes)
    s.add(If(day == 0, start >= 720, True))
    
    # Function to get busy intervals for a participant on a specific day
    def get_busy_intervals(participant, d):
        if participant == 'Joshua':
            if d == 0:  # Monday
                return [(15*60, 15*60 + 30)]  # 15:00 to 15:30
            elif d == 1:  # Tuesday
                return [(11*60 + 30, 12*60),      # 11:30 to 12:00
                        (13*60, 13*60 + 30),      # 13:00 to 13:30
                        (14*60 + 30, 15*60)]      # 14:30 to 15:00
            elif d == 2:  # Wednesday
                return []
        elif participant == 'Joyce':
            if d == 0:  # Monday
                return [(9*60, 9*60 + 30),        # 9:00 to 9:30
                        (10*60, 11*60),           # 10:00 to 11:00
                        (11*60 + 30, 12*60 + 30), # 11:30 to 12:30
                        (13*60, 15*60),           # 13:00 to 15:00
                        (15*60 + 30, 17*60)]      # 15:30 to 17:00
            elif d == 1:  # Tuesday
                return [(9*60, 17*60)]            # 9:00 to 17:00
            elif d == 2:  # Wednesday
                return [(9*60, 9*60 + 30),        # 9:00 to 9:30
                        (10*60, 11*60),           # 10:00 to 11:00
                        (12*60 + 30, 15*60 + 30), # 12:30 to 15:30
                        (16*60, 16*60 + 30)]      # 16:00 to 16:30
    
    # Add constraints for both participants
    for participant in ['Joshua', 'Joyce']:
        for d in [0, 1, 2]:
            intervals = get_busy_intervals(participant=participant, d=d)
            for (s_busy, e_busy) in intervals:
                # Non-overlap condition: meeting ends before busy starts OR meeting starts after busy ends
                non_overlap = Or(start + 30 <= s_busy, start >= e_busy)
                s.add(If(day == d, non_overlap, True))
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        d_val = m[day].as_long()
        start_val = m[start].as_long()
        days = ['Monday', 'Tuesday', 'Wednesday']
        day_str = days[d_val]
        # Convert start time to HH:MM format
        hour = start_val // 60
        minute = start_val % 60
        start_time = f"{hour:02d}:{minute:02d}"
        end_val = start_val + 30
        hour_end = end_val // 60
        minute_end = end_val % 60
        end_time = f"{hour_end:02d}:{minute_end:02d}"
        print(f"Day: {day_str}")
        print(f"Start time: {start_time}")
        print(f"End time: {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()