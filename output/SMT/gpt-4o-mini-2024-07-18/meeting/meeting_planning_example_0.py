from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define the time parameters
arrival_time = 9 * 60  # Arrive at Marina District at 9:00 AM (in minutes)
departure_time = 17 * 60  # Assume you need to leave by 5:00 PM (in minutes)

# Stephanie's availability
stephanie_start = (10 + 30)  # 10:30 AM in minutes
stephanie_end = (13 + 30)     # 1:30 PM in minutes
min_meeting_duration = 120     # Minimum meeting duration in minutes

# Define the travel times
travel_time_to_mission = 20  # Marina to Mission
travel_time_to_marina = 19    # Mission to Marina

# Meeting start time in Mission
meeting_start = Int('meeting_start')

# Constraints for the meeting time
s.add(meeting_start >= arrival_time + travel_time_to_mission)  # Must arrive at Mission after travel
s.add(meeting_start >= stephanie_start)                        # Must arrive after Stephanie's availability starts
s.add(meeting_start + min_meeting_duration <= stephanie_end)  # Must leave before Stephanie's availability ends

# Total time until departure
s.add(meeting_start + min_meeting_duration <= departure_time - travel_time_to_marina)  # Must finish meeting to go back to Marina

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    meeting_start_time = model[meeting_start].as_long()
    meeting_end_time = meeting_start_time + min_meeting_duration  # Calculate when you leave the meeting.

    print("Trip plan is possible with the following details:")
    print(f"Meeting starts at: {meeting_start_time // 60}:{meeting_start_time % 60:02d}")
    print(f"Meeting ends at: {meeting_end_time // 60}:{meeting_end_time % 60:02d}")

else:
    print("No possible trip plan found.")