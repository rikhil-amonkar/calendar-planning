from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define the constants for travel and timing
arrival_time = 9 * 60  # Arrival at Chinatown at 9:00 AM (in minutes)
travel_time_to_russian_hill = 7  # Travel time from Chinatown to Russian Hill (in minutes)
travel_time_back = 9               # Travel time from Russian Hill back to Chinatown (in minutes)

# Ronald's availability
ronald_start = 15 * 60 + 15  # Ronald is at Russian Hill starting at 3:15 PM (in minutes, 915 minutes)
ronald_end = 21 * 60 + 30    # Ronald leaves at 9:30 PM (in minutes, 1290 minutes)
min_meeting_duration = 105     # Minimum meeting duration in minutes

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for the meeting time
s.add(meeting_start >= arrival_time + travel_time_to_russian_hill)  # Must arrive at Russian Hill after travel
s.add(meeting_start >= ronald_start)                                # Meeting must start after Ronald is available
s.add(meeting_start + min_meeting_duration <= ronald_end)          # Meeting must finish before Ronald leaves

# Add a constraint to ensure there is enough time to return after the meeting
s.add(meeting_start + min_meeting_duration + travel_time_back <= 24 * 60)  # Must finish before midnight

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + min_meeting_duration  # Calculate end time of the meeting

    print("SOLUTION:")
    print(f"Meeting starts at: {start_time // 60}:{start_time % 60:02d}")
    print(f"Meeting ends at: {end_time // 60}:{end_time % 60:02d}")
else:
    print("No possible trip plan found.")