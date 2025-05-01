from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for timing and travel
arrival_time = 9 * 60  # Arrival at Chinatown at 9:00 AM (540 minutes)
travel_time_to_marina = 12  # Travel time from Chinatown to Marina District (in minutes)
travel_time_back = 16       # Travel time from Marina District back to Chinatown (in minutes)

# Stephanie's availability
stephanie_start = 8 * 60  # Stephanie is at Marina District starting at 8:00 AM (480 minutes)
stephanie_end = 15 * 60    # Stephanie leaves Marina District at 3:00 PM (900 minutes)
min_meeting_duration = 105  # Minimum meeting duration (in minutes)

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for meeting time
s.add(meeting_start >= arrival_time + travel_time_to_marina)  # Must arrive at Marina after travel
s.add(meeting_start >= stephanie_start)                        # Meeting must start after Stephanie is available
s.add(meeting_start + min_meeting_duration <= stephanie_end)  # Meeting must finish before Stephanie leaves

# Add a constraint to ensure you have enough time to return after the meeting is over
s.add(meeting_start + min_meeting_duration + travel_time_back <= 24 * 60)  # Must finish before midnight

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + min_meeting_duration  # Calculate when you will leave the meeting.

    print("SOLUTION:")
    print(f"Meeting starts at: {start_time // 60}:{start_time % 60:02d}")
    print(f"Meeting ends at: {end_time // 60}:{end_time % 60:02d}")
else:
    print("No possible trip plan found.")