from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for timing and travel
arrival_time = 9 * 60  # Arrival at The Castro at 9:00 AM (in minutes)
travel_time_to_ggpark = 11  # Travel time from The Castro to Golden Gate Park (in minutes)
travel_time_back = 13         # Travel time from Golden Gate Park back to The Castro (in minutes)

# Jeffrey's availability
jeffrey_start = 7 * 60      # Jeffrey is at Golden Gate Park from 7:00 AM (in minutes)
jeffrey_end = 17 * 60 + 30   # Jeffrey leaves at 5:30 PM (in minutes)
min_meeting_duration = 105    # Minimum meeting duration in minutes

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for meeting time
s.add(meeting_start >= arrival_time + travel_time_to_ggpark)  # Must arrive at Golden Gate Park after traveling
s.add(meeting_start >= jeffrey_start)                          # Meeting must start after Jeffrey is available
s.add(meeting_start + min_meeting_duration <= jeffrey_end)     # Meeting must finish before Jeffrey leaves

# Add a constraint to ensure there is enough time to return after the meeting is over
s.add(meeting_start + min_meeting_duration + travel_time_back <= 24 * 60)  # Must finish before midnight

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + min_meeting_duration  # Calculate the end time of the meeting.

    print("SOLUTION:")
    print(f"Meeting starts at: {start_time // 60}:{start_time % 60:02d}")
    print(f"Meeting ends at: {end_time // 60}:{end_time % 60:02d}")
else:
    print("No possible trip plan found.")