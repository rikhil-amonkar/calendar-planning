from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for travel times
travel_time_to_union_square = 30  # Travel time from Sunset District to Union Square (in minutes)
travel_time_back = 26               # Travel time from Union Square back to Sunset District (in minutes)

# Constants for arrival and availability
arrival_time = 9 * 60              # Arrival at Sunset District at 9:00 AM (540 minutes)
sarah_start = 12 * 60 + 30         # Sarah is at Union Square from 12:30 PM (750 minutes)
sarah_end = 21 * 60 + 30           # Sarah leaves at 9:30 PM (1290 minutes)
min_meeting_duration = 15           # Minimum meeting duration (in minutes)

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for the meeting time
s.add(meeting_start >= arrival_time + travel_time_to_union_square)  # Must arrive at Union Square after traveling
s.add(meeting_start >= sarah_start)                                  # Meeting must start after Sarah arrives
s.add(meeting_start + min_meeting_duration <= sarah_end)            # Meeting must finish before Sarah leaves

# Ensure there's enough time to return after the meeting
s.add(meeting_start + min_meeting_duration + travel_time_back <= 24 * 60)  # Must finish before midnight

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + min_meeting_duration  # Calculate end time of meeting

    print("SOLUTION:")
    print(f"Meeting starts at: {start_time // 60}:{start_time % 60:02d}")
    print(f"Meeting ends at: {end_time // 60}:{end_time % 60:02d}")
else:
    print("No possible trip plan found.")