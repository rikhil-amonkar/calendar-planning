from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for time and travel distances
arrival_time = 9 * 60  # Arrival at Bayview at 9:00 AM (540 minutes)
travel_time_to_financial = 19  # Travel time from Bayview to Financial District (in minutes)
travel_time_back = 19            # Travel time from Financial District back to Bayview (in minutes)

# Jeffrey's availability
jeffrey_start = 12 * 60 + 15  # Jeffrey will be at Financial District from 12:15 PM (735 minutes)
jeffrey_end = 14 * 60          # Jeffrey leaves at 2:00 PM (840 minutes)
min_meeting_duration = 90       # Minimum meeting duration in minutes

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for the meeting time
s.add(meeting_start >= arrival_time + travel_time_to_financial)  # Must arrive at Financial District after travel
s.add(meeting_start >= jeffrey_start)                           # Meeting must start after Jeffrey is available
s.add(meeting_start + min_meeting_duration <= jeffrey_end)      # Meeting must finish before Jeffrey leaves

# Add a constraint to ensure there is enough time to return after the meeting
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