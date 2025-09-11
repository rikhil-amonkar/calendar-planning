from z3 import *

def main():
    # Initialize solver
    s = Solver()
    
    # Meeting duration in minutes
    meeting_duration = 30
    
    # Total available minutes (9:00 to 17:00 is 8 hours = 480 minutes)
    total_minutes = 480
    
    # Start time variable (in minutes from 9:00)
    start = Int('start')
    
    # Constraint: start time must be within working hours and allow meeting to end by 17:00
    s.add(start >= 0, start <= total_minutes - meeting_duration)
    
    # Convert busy intervals to minutes from 9:00
    # Andrea: 9:30-10:30, 13:30-14:30
    andrea_busy = [(30, 90), (270, 330)]
    # Ruth: 12:30-13:00, 15:00-15:30
    ruth_busy = [(150, 180), (240, 270)]
    # Steven: 10:00-10:30, 11:00-11:30, 12:00-12:30, 13:30-14:00, 15:00-16:00
    steven_busy = [(60, 90), (120, 150), (180, 210), (270, 300), (240, 300)]
    # Grace: no meetings
    grace_busy = []
    # Kyle: 9:00-9:30, 10:30-12:00, 12:30-13:00, 13:30-15:00, 15:30-16:00, 16:30-17:00
    kyle_busy = [(0, 30), (90, 180), (150, 180), (270, 360), (330, 360), (390, 480)]
    # Elijah: 9:00-11:00, 11:30-13:00, 13:30-14:00, 15:30-16:00, 16:30-17:00
    elijah_busy = [(0, 120), (150, 240), (270, 300), (330, 360), (390, 480)]
    # Lori: 9:00-9:30, 10:00-11:30, 12:00-13:30, 14:00-16:00, 16:30-17:00
    lori_busy = [(0, 30), (60, 150), (180, 270), (300, 420), (390, 480)]
    
    # Combine all schedules
    all_busy = andrea_busy + ruth_busy + steven_busy + grace_busy + kyle_busy + elijah_busy + lori_busy
    
    # Add constraints for each busy interval
    for (busy_start, busy_end) in all_busy:
        # Meeting must not overlap: either end before busy start or start after busy end
        s.add(Or(start + meeting_duration <= busy_start, start >= busy_end))
    
    # Check for solution
    if s.check() == sat:
        m = s.model()
        start_minutes = m.evaluate(start).as_long()
        
        # Convert start minutes to time string
        start_hour = 9 + start_minutes // 60
        start_minute = start_minutes % 60
        end_minutes = start_minutes + meeting_duration
        end_hour = 9 + end_minutes // 60
        end_minute = end_minutes % 60
        
        # Format output
        time_str = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
        print(f"Monday:{time_str}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()