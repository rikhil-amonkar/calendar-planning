from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for timing and travel
arrival_time = 9 * 60            # Arrival at Golden Gate Park at 9:00 AM (in minutes)
travel_time_to_marina = 16       # Travel time from Golden Gate Park to Marina District (in minutes)
travel_time_back = 18             # Travel time from Marina District back to Golden Gate Park (in minutes)

# James's availability
james_start = 10 * 60 + 15       # James is at Marina District starting at 10:15 AM (615 minutes)
james_end = 13 * 60 + 30         # James leaves at 1:30 PM (810 minutes)
min_meeting_duration = 15         # Minimum meeting duration in minutes

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for the meeting time
s.add(meeting_start >= arrival_time + travel_time_to_marina)  # Must arrive at Marina after travel
s.add(meeting_start >= james_start)                            # Meeting must start after James is available
s.add(meeting_start + min_meeting_duration <= james_end)      # Meeting must finish before James leaves

# Add a constraint to ensure you have time to return after the meeting
s.add(meeting_start + min_meeting_duration + travel_time_back <= 24 * 60)  # Must finish before midnight

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + min_meeting_duration  # Calculate when you will leave the meeting

    print("SOLUTION:")
    print(f"Meeting starts at: {start_time // 60}:{start_time % 60:02d}")
    print(f"Meeting ends at: {end_time // 60}:{end_time % 60:02d}")
else:
    print("No possible trip plan found.")