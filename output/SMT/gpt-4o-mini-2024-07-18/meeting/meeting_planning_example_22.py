from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define travel times
travel_time_to_union_square = 22  # Travel time from Presidio to Union Square (in minutes)
travel_time_back = 24               # Travel time from Union Square back to Presidio (in minutes)

# Constants for timing
arrival_time = 9 * 60              # Arrival at Presidio at 9:00 AM (540 minutes)
andrew_start = 11 * 60 + 15        # Andrew will be at Union Square from 11:15 AM (675 minutes)
andrew_end = 17 * 60 + 15          # Andrew leaves at 5:15 PM (1035 minutes)
min_meeting_duration = 105          # Minimum meeting duration in minutes

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for meeting time
s.add(meeting_start >= arrival_time + travel_time_to_union_square)  # Must arrive at Union Square after traveling
s.add(meeting_start >= andrew_start)                                  # Meeting must start after Andrew is available
s.add(meeting_start + min_meeting_duration <= andrew_end)            # Meeting must finish before Andrew leaves

# Add a constraint to ensure you can return to Presidio after the meeting
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