from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for travel times
travel_time_to_bayview = 22  # Travel time from North Beach to Bayview (in minutes)
travel_time_back = 21        # Travel time from Bayview back to North Beach (in minutes)

# Constants for timing
arrival_time = 9 * 60          # Arrival at North Beach at 9:00 AM (540 minutes)
paul_start = 13 * 60 + 30      # Paul will be at Bayview from 1:30 PM (810 minutes)
paul_end = 19 * 60 + 45        # Paul leaves at 7:45 PM (1185 minutes)
min_meeting_duration = 45       # Minimum meeting duration (in minutes)

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for meeting time
s.add(meeting_start >= arrival_time + travel_time_to_bayview)  # Must arrive at Bayview after traveling
s.add(meeting_start >= paul_start)                             # Meeting must start after Paul is available
s.add(meeting_start + min_meeting_duration <= paul_end)       # Meeting must finish before Paul leaves

# Add a constraint to ensure there is enough time to return after the meeting is over
s.add(meeting_start + min_meeting_duration + travel_time_back <= 24 * 60)  # Must finish before midnight

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + min_meeting_duration  # Calculate when you finish the meeting.

    print("SOLUTION:")
    print(f"Meeting starts at: {start_time // 60}:{start_time % 60:02d}")  # Format time as HH:MM
    print(f"Meeting ends at: {end_time // 60}:{end_time % 60:02d}")      # Format time as HH:MM
else:
    print("No possible trip plan found.")