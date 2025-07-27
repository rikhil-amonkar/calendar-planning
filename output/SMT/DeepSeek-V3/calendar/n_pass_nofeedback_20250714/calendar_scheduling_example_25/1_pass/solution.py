from z3 import *

def solve_scheduling():
    # Participants' busy times on Monday in minutes since 9:00 (540 minutes is 9:00)
    # Work hours: 9:00 (540) to 17:00 (1020)
    
    # Convert all times to minutes since 0:00 for easier handling
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm
    
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"
    
    work_start = time_to_minutes("09:00")
    work_end = time_to_minutes("17:00")
    meeting_duration = 60  # minutes
    
    # Busy intervals for each participant in minutes since 0:00
    anthony_busy = [
        (time_to_minutes("09:30"), time_to_minutes("10:00")),
        (time_to_minutes("12:00"), time_to_minutes("13:00")),
        (time_to_minutes("16:00"), time_to_minutes("16:30"))
    ]
    
    pamela_busy = [
        (time_to_minutes("09:30"), time_to_minutes("10:00")),
        (time_to_minutes("16:30"), time_to_minutes("17:00"))
    ]
    
    zachary_busy = [
        (time_to_minutes("09:00"), time_to_minutes("11:30")),
        (time_to_minutes("12:00"), time_to_minutes("12:30")),
        (time_to_minutes("13:00"), time_to_minutes("13:30")),
        (time_to_minutes("14:30"), time_to_minutes("15:00")),
        (time_to_minutes("16:00"), time_to_minutes("17:00"))
    ]
    
    # Pamela's preference: not after 14:30 (870 minutes)
    pamela_preference_max = time_to_minutes("14:30")
    
    # Create a solver instance
    s = Solver()
    
    # The meeting start time in minutes since 0:00
    meeting_start = Int('meeting_start')
    
    # Constraints: meeting must be within work hours and duration fits
    s.add(meeting_start >= work_start)
    s.add(meeting_start + meeting_duration <= work_end)
    
    # Function to check if a time interval overlaps with any busy interval
    def is_available(start, duration, busy_intervals):
        # The meeting interval is [start, start + duration)
        meeting_end = start + duration
        # For each busy interval, the meeting must not overlap
        for (busy_start, busy_end) in busy_intervals:
            # Overlap occurs if meeting starts before busy ends and meeting ends after busy starts
            s.add(Not(And(meeting_start < busy_end, meeting_start + meeting_duration > busy_start)))
    
    # Apply availability constraints for each participant
    is_available(meeting_start, meeting_duration, anthony_busy)
    is_available(meeting_start, meeting_duration, pamela_busy)
    is_available(meeting_start, meeting_duration, zachary_busy)
    
    # Pamela's preference: meeting must end by 14:30
    s.add(meeting_start + meeting_duration <= pamela_preference_max)
    
    # Check if there's a solution
    if s.check() == sat:
        m = s.model()
        start_time_min = m[meeting_start].as_long()
        end_time_min = start_time_min + meeting_duration
        start_time = minutes_to_time(start_time_min)
        end_time = minutes_to_time(end_time_min)
        
        print("SOLUTION:")
        print(f"Day: Monday")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found")

solve_scheduling()