from z3 import *

def main():
    # Create solver
    s = Solver()
    
    # Define variables
    day = Int('day')
    start_minutes = Int('start_minutes')
    
    # Day encoding: 0=Monday, 1=Tuesday, 2=Wednesday
    days = [0, 1, 2]
    day_names = ['Monday', 'Tuesday', 'Wednesday']
    
    # Work hours: 9:00 to 17:00 (540 to 1020 minutes)
    work_start = 540
    work_end = 1020
    meeting_duration = 30
    
    # Susan's blocked times (in minutes from midnight)
    susan_busy = {
        0: [(12*60+30, 13*60), (13*60+30, 14*60)],  # Monday
        1: [(11*60+30, 12*60)],                      # Tuesday
        2: [(9*60+30, 10*60+30), (14*60, 14*60+30), (15*60+30, 16*60+30)]  # Wednesday
    }
    
    # Sandra's blocked times (including constraint: no Monday after 16:00)
    sandra_busy = {
        0: [(9*60, 13*60), (14*60, 15*60), (16*60, 17*60)],  # Monday (added 16:00-17:00)
        1: [(9*60, 9*60+30), (10*60+30, 12*60), (12*60+30, 13*60+30), (14*60, 14*60+30), (16*60, 17*60)],
        2: [(9*60, 11*60+30), (12*60, 12*60+30), (13*60, 17*60)]
    }
    
    # Basic constraints
    s.add(Or([day == d for d in days]))
    s.add(start_minutes >= work_start)
    s.add(start_minutes + meeting_duration <= work_end)
    
    # Avoid Tuesday if possible (soft constraint)
    s.add(day != 1)
    
    # Function to check overlap with busy intervals
    def no_overlap(start, duration, intervals):
        return And([Or(start >= end, start + duration <= begin) for (begin, end) in intervals])
    
    # Add constraints for each day
    for d in days:
        # Susan's availability for day d
        susan_free = no_overlap(start_minutes, meeting_duration, susan_busy.get(d, []))
        # Sandra's availability for day d
        sandra_free = no_overlap(start_minutes, meeting_duration, sandra_busy.get(d, []))
        # If meeting is on day d, both must be free
        s.add(If(day == d, And(susan_free, sandra_free), True))
    
    # Check solution avoiding Tuesday
    if s.check() == sat:
        m = s.model()
        d = m[day].as_long()
        start = m[start_minutes].as_long()
    else:
        # Try including Tuesday
        s2 = Solver()
        s2.add(Or([day == d for d in days]))
        s2.add(start_minutes >= work_start)
        s2.add(start_minutes + meeting_duration <= work_end)
        for d in days:
            susan_free = no_overlap(start_minutes, meeting_duration, susan_busy.get(d, []))
            sandra_free = no_overlap(start_minutes, meeting_duration, sandra_busy.get(d, []))
            s2.add(If(day == d, And(susan_free, sandra_free), True))
        s2.check()
        m = s2.model()
        d = m[day].as_long()
        start = m[start_minutes].as_long()
    
    # Calculate end time
    end = start + meeting_duration
    # Convert minutes to HH:MM format
    def format_time(minutes):
        h = minutes // 60
        m = minutes % 60
        return f"{h:02d}:{m:02d}"
    
    start_str = format_time(start)
    end_str = format_time(end)
    day_str = day_names[d]
    
    print(f"{day_str} {start_str}:{end_str}")

if __name__ == "__main__":
    main()