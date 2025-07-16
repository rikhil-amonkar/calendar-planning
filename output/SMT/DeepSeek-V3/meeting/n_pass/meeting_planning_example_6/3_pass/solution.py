from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Convert all times to minutes since midnight
    arrival_time = 9 * 60  # 9:00 AM (540 minutes)
    kenneth_start = 14 * 60 + 15  # 2:15 PM (855 minutes)
    kenneth_end = 19 * 60 + 45    # 7:45 PM (1185 minutes)
    travel_time = 11  # minutes

    # Meeting variables (minutes since midnight)
    meeting_start = Int('meeting_start')
    meeting_end = Int('meeting_end')

    # Add bounds to prevent malformed output
    s.add(meeting_start >= 0, meeting_start <= 1440)  # Within one day
    s.add(meeting_end >= 0, meeting_end <= 1440)      # Within one day

    # Core constraints
    s.add(meeting_start >= kenneth_start)
    s.add(meeting_end <= kenneth_end)
    s.add(meeting_end - meeting_start >= 90)  # Minimum 90 minute meeting
    s.add(meeting_start + travel_time >= arrival_time)  # Can't travel before arriving

    # Additional constraints to ensure valid times
    s.add(meeting_start < meeting_end)
    s.add(meeting_start <= kenneth_end - 90)  # Must have time for full meeting

    if s.check() == sat:
        m = s.model()
        try:
            start = m[meeting_start].as_long()
            end = m[meeting_end].as_long()
            
            # Convert to 12-hour format with AM/PM
            def format_time(minutes):
                hours = minutes // 60
                mins = minutes % 60
                period = "AM" if hours < 12 else "PM"
                if hours > 12:
                    hours -= 12
                elif hours == 0:
                    hours = 12
                return f"{hours}:{mins:02d} {period}"
            
            print(f"Optimal meeting time: {format_time(start)} to {format_time(end)}")
        except:
            print("Error in processing solution")
    else:
        print("No valid schedule found")

solve_scheduling()