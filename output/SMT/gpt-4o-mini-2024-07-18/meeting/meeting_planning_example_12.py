from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for time and travel
arrival_time = 9 * 60  # Arrival at North Beach at 9:00 AM (in minutes)
travel_time_to_alamo = 16  # Travel time from North Beach to Alamo Square (in minutes)
travel_time_back = 15      # Travel time from Alamo Square back to North Beach (in minutes)

# Barbara's availability
barbara_start = 18 * 60  # Barbara is at Alamo Square starting at 6:00 PM (in minutes)
barbara_end = 21 * 60 + 30  # Barbara leaves at 9:30 PM (in minutes)
min_meeting_duration = 90    # Minimum meeting duration in minutes

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for meeting time
s.add(meeting_start >= arrival_time + travel_time_to_alamo)  # Must arrive at Alamo Square after traveling
s.add(meeting_start >= barbara_start)                        # Meeting must start after Barbara is available
s.add(meeting_start + min_meeting_duration <= barbara_end)  # Meeting must finish before Barbara leaves

# Add a constraint to ensure you have enough time to return after the meeting
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