import json

def format_time(minutes):
    """Convert minutes since midnight to H:MM (24-hour) format without a leading zero for hours."""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Travel times in minutes between locations
travel_NB_to_PH = 8      # North Beach -> Pacific Heights
travel_NB_to_EM = 6      # North Beach -> Embarcadero
travel_PH_to_NB = 9      # Pacific Heights -> North Beach
travel_PH_to_EM = 10     # Pacific Heights -> Embarcadero
travel_EM_to_NB = 5      # Embarcadero -> North Beach
travel_EM_to_PH = 11     # Embarcadero -> Pacific Heights

# Arrival time at North Beach (in minutes from midnight)
arrival_NB = 9 * 60  # 9:00 AM -> 540 minutes

# Karen's meeting constraints
karen_location = "Pacific Heights"
karen_available_start = 18 * 60 + 45  # 18:45 -> 1125 minutes
karen_available_end   = 20 * 60 + 15  # 20:15 -> 1215 minutes
karen_min_duration = 90  # minutes

# Mark's meeting constraints
mark_location = "Embarcadero"
mark_available_start = 13 * 60  # 13:00 -> 780 minutes
mark_available_end = 17 * 60 + 45  # 17:45 -> 1065 minutes
mark_min_duration = 120  # minutes

# For an optimal schedule that maximizes friend meeting time,
# we plan to start Mark's meeting as early as possible (at his available start)
# and extend it to the full duration of his availability.
mark_meeting_start = mark_available_start  # 780 minutes (13:00)
mark_meeting_end = mark_available_end        # 1065 minutes (17:45)

# Ensure Mark's meeting duration meets the minimum requirement
if mark_meeting_end - mark_meeting_start < mark_min_duration:
    raise ValueError("Mark's meeting duration does not meet the minimum requirement!")

# Karen's meeting is fixed to her available window
karen_meeting_start = karen_available_start  # 1125 minutes (18:45)
karen_meeting_end = karen_available_end        # 1215 minutes (20:15)
if karen_meeting_end - karen_meeting_start < karen_min_duration:
    raise ValueError("Karen's meeting duration does not meet the minimum requirement!")

# Compute departure from North Beach to Embarcadero such that you arrive by Mark's meeting start.
depart_NB_to_EM = mark_meeting_start - travel_NB_to_EM  # 780 - 6 = 774 minutes (12:54)
arrival_EM = depart_NB_to_EM + travel_NB_to_EM  # Should equal mark_meeting_start (780 minutes)

# After finishing Mark's meeting, travel from Embarcadero to Pacific Heights.
depart_EM_to_PH = mark_meeting_end  # 1065 minutes (17:45)
arrival_PH = depart_EM_to_PH + travel_EM_to_PH  # 1065 + 11 = 1076 minutes (17:56)

# Although arrival at Pacific Heights is at 17:56, Karen is only available starting at 18:45.
# You will wait until her meeting time begins.

# Build the meeting itinerary
itinerary = [
    {
        "action": "meet",
        "location": mark_location,
        "person": "Mark",
        "start_time": format_time(mark_meeting_start),
        "end_time": format_time(mark_meeting_end)
    },
    {
        "action": "meet",
        "location": karen_location,
        "person": "Karen",
        "start_time": format_time(karen_meeting_start),
        "end_time": format_time(karen_meeting_end)
    }
]

# Final schedule dictionary
schedule = {
    "itinerary": itinerary
}

# Output the schedule as a JSON-formatted string
print(json.dumps(schedule, indent=2))