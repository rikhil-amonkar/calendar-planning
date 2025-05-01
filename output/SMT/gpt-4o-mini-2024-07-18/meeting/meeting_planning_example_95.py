from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for travel times
travel_time_to_bayview = 22  # Travel time from North Beach to Bayview (in minutes)
travel_time_back = 21         # Travel time from Bayview back to North Beach (in minutes)

# Constants for timing
arrival_time = 9 * 60        # Arrival at North Beach at 9:00 AM (540 minutes)
steven_start = 11 * 60       # Steven will be at Bayview from 11:00 AM (660 minutes)
steven_end = 12 * 60 + 45    # Steven leaves at 12:45 PM (765 minutes)
min_meeting_duration = 90     # Minimum meeting duration (in minutes)

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for meeting time
s.add(meeting_start >= arrival_time + travel_time_to_bayview)  # Must arrive at Bayview after traveling
s.add(meeting_start >= steven_start)                           # Meeting must start after Steven is available
s.add(meeting_start + min_meeting_duration <= steven_end)     # Meeting must finish before Steven leaves

# Ensure there is enough time to return after the meeting
s.add(meeting_start + min_meeting_duration + travel_time_back <= 24 * 60)  # Must finish before midnight

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + min_meeting_duration  # Calculate when the meeting will end

    print("SOLUTION:")
    print(f"Meeting starts at: {start_time // 60}:{start_time % 60:02d}")  # Format time as HH:MM
    print(f"Meeting ends at: {end_time // 60}:{end_time % 60:02d}")      # Format time as HH:MM
else:
    print("No possible trip plan found.")