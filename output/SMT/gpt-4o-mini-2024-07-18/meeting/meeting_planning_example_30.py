from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for travel times and timings
travel_time_to_north_beach = 17  # Travel time from Richmond District to North Beach (in minutes)
travel_time_back = 18              # Travel time from North Beach back to Richmond District (in minutes)

# Constants for availability
arrival_time = 9 * 60             # Arrival at Richmond District at 9:00 AM (in minutes, 540)
stephanie_start = 9 * 60 + 30     # Stephanie is at North Beach starting at 9:30 AM (570 minutes)
stephanie_end = 16 * 60 + 15       # Stephanie leaves North Beach at 4:15 PM (975 minutes)
min_meeting_duration = 120          # Minimum meeting duration in minutes

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for meeting time
s.add(meeting_start >= arrival_time + travel_time_to_north_beach)  # Must arrive at North Beach after traveling
s.add(meeting_start >= stephanie_start)                             # Meeting must start after Stephanie arrives
s.add(meeting_start + min_meeting_duration <= stephanie_end)       # Meeting must finish before Stephanie leaves

# Add a constraint to ensure you have enough time to return after the meeting is over
s.add(meeting_start + min_meeting_duration + travel_time_back <= 24 * 60)  # Must finish before midnight

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + min_meeting_duration  # Calculate the end time of the meeting

    print("SOLUTION:")
    print(f"Meeting starts at: {start_time // 60}:{start_time % 60:02d}")
    print(f"Meeting ends at: {end_time // 60}:{end_time % 60:02d}")
else:
    print("No possible trip plan found.")