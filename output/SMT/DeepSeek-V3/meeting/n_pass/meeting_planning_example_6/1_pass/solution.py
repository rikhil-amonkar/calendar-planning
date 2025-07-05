from z3 import *

def solve_scheduling_problem():
    # Initialize the solver
    s = Solver()

    # Convert all times to minutes since 9:00 AM (540 minutes since midnight)
    # Kenneth's availability: 2:15 PM to 7:45 PM
    # 2:15 PM is 14*60 + 15 = 855 minutes since midnight, so 855 - 540 = 315 minutes since 9:00 AM
    # 7:45 PM is 19*60 + 45 = 1185 minutes since midnight, so 1185 - 540 = 645 minutes since 9:00 AM
    kenneth_start_min = 315  # 2:15 PM relative to 9:00 AM
    kenneth_end_min = 645    # 7:45 PM relative to 9:00 AM

    # Meeting start and end times (relative to 9:00 AM)
    meeting_start = Int('meeting_start')
    meeting_end = Int('meeting_end')

    # Travel time from Fisherman's Wharf to Nob Hill is 11 minutes
    travel_time = 11

    # Constraints
    # 1. Meeting must start and end within Kenneth's availability
    s.add(meeting_start >= kenneth_start_min)
    s.add(meeting_end <= kenneth_end_min)
    # 2. Meeting duration must be at least 90 minutes
    s.add(meeting_end - meeting_start >= 90)
    # 3. Must arrive at Nob Hill by meeting_start, leaving Fisherman's Wharf at (meeting_start - travel_time)
    # Since we start at Fisherman's Wharf at time 0 (9:00 AM), the earliest we can leave is time 0.
    s.add(meeting_start - travel_time >= 0)

    # Check if the constraints are satisfiable
    if s.check() == sat:
        m = s.model()
        start = m[meeting_start].as_long()
        end = m[meeting_end].as_long()
        duration = end - start

        # Convert times back to HH:MM format
        def to_time_str(minutes):
            total_minutes = 540 + minutes  # 9:00 AM is 540 minutes
            hours = total_minutes // 60
            mins = total_minutes % 60
            return f"{hours}:{mins:02d}"

        start_time = to_time_str(start)
        end_time = to_time_str(end)
        travel_departure_time = to_time_str(start - travel_time)

        print(f"Optimal meeting schedule:")
        print(f"Leave Fisherman's Wharf at: {travel_departure_time}")
        print(f"Arrive at Nob Hill by: {start_time}")
        print(f"Meet Kenneth from: {start_time} to {end_time} (Duration: {duration} minutes)")
    else:
        print("No feasible schedule found.")

solve_scheduling_problem()