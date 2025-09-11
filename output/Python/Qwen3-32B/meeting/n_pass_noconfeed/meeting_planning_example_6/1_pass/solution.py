import json

def minutes_to_time(total_minutes):
    hours = total_minutes // 60
    minutes = total_minutes % 60
    return f"{hours}:{minutes:02d}"

# Input parameters
start_location = "Fisherman's Wharf"
start_time_minutes = 9 * 60  # 9:00 AM
kenneth_location = "Nob Hill"
kenneth_start_minutes = 14 * 60 + 15  # 2:15 PM
kenneth_end_minutes = 19 * 60 + 45  # 7:45 PM
min_meeting_duration = 90  # minutes
travel_time_wharf_to_nob = 11  # minutes

# Calculate earliest possible arrival at Nob Hill (Kenneth's start time)
arrival_nob_hill = kenneth_start_minutes
departure_wharf = arrival_nob_hill - travel_time_wharf_to_nob

itinerary = []

# Check if departure from Wharf is feasible
if departure_wharf >= start_time_minutes:
    # Check if meeting can fit in Kenneth's schedule
    meeting_start = arrival_nob_hill
    meeting_end = meeting_start + min_meeting_duration
    if meeting_end <= kenneth_end_minutes:
        start_time_str = minutes_to_time(meeting_start)
        end_time_str = minutes_to_time(meeting_end)
        itinerary.append({
            "action": "meet",
            "location": kenneth_location,
            "person": "Kenneth",
            "start_time": start_time_str,
            "end_time": end_time_str
        })

result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))