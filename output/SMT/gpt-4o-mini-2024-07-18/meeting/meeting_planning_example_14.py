from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for timing and travel
arrival_time = 9 * 60               # Arrive at Nob Hill at 9:00 AM (540 minutes)
travel_time_to_marina = 11          # Travel time from Nob Hill to Marina District (in minutes)
travel_time_back = 12                # Travel time from Marina District back to Nob Hill (in minutes)

# Mary's availability
mary_start = 20 * 60                 # Mary is at Marina District starting at 8:00 PM (1200 minutes)
mary_end = 22 * 60                   # Mary leaves at 10:00 PM (1200 minutes)
min_meeting_duration = 120            # Minimum meeting duration (in minutes)

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for meeting time
s.add(meeting_start >= arrival_time + travel_time_to_marina)  # Must arrive at Marina after travelling
s.add(meeting_start >= mary_start)                            # Meeting must start after Mary is available
s.add(meeting_start + min_meeting_duration <= mary_end)      # Meeting must finish before Mary leaves

# Add a constraint to ensure you have time to return after the meeting
s.add(meeting_start + min_meeting_duration + travel_time_back <= 24 * 60)  # Must finish before midnight

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + min_meeting_duration  # Calculate when you will finish the meeting.

    print("SOLUTION:")
    print(f"Meeting starts at: {start_time // 60}:{start_time % 60:02d}")
    print(f"Meeting ends at: {end_time // 60}:{end_time % 60:02d}")
else:
    print("No possible trip plan found.")