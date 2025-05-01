from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for travel times
travel_time_to_castro = 19  # Travel time from Union Square to The Castro (in minutes)
travel_time_back = 19         # Travel time from The Castro back to Union Square (in minutes)

# Constants for timing
arrival_time = 9 * 60        # Arrival at Union Square at 9:00 AM (540 minutes)
michelle_start = 18 * 60     # Michelle is at The Castro from 6:00 PM (1080 minutes)
michelle_end = 20 * 60       # Michelle leaves at 8:00 PM (1200 minutes)
min_meeting_duration = 105    # Minimum meeting duration (in minutes)

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for meeting time
s.add(meeting_start >= arrival_time + travel_time_to_castro)  # Must arrive at The Castro after traveling
s.add(meeting_start >= michelle_start)                          # Meeting must start after Michelle is available
s.add(meeting_start + min_meeting_duration <= michelle_end)    # Meeting must finish before Michelle leaves

# Ensure there is enough time to return after the meeting
s.add(meeting_start + min_meeting_duration + travel_time_back <= 24 * 60)  # Must finish before midnight

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + min_meeting_duration  # Calculate end time of the meeting

    print("SOLUTION:")
    print(f"Meeting starts at: {start_time // 60}:{start_time % 60:02d}")  # Format time as HH:MM
    print(f"Meeting ends at: {end_time // 60}:{end_time % 60:02d}")      # Format time as HH:MM
else:
    print("No possible trip plan found.")