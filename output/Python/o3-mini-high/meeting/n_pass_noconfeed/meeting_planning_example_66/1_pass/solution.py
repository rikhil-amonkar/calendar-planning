import json

def minutes_to_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

def main():
    # Input parameters (all times are represented in minutes after midnight)
    arrival_time_nob_hill = 9 * 60  # 9:00AM at Nob Hill (540 minutes)
    travel_nobhill_to_presidio = 17  # minutes from Nob Hill to Presidio
    travel_presidio_to_nobhill = 18  # minutes from Presidio to Nob Hill
    robert_available_start = 11 * 60 + 15  # 11:15AM in minutes (675 minutes)
    robert_available_end = 17 * 60 + 45      # 5:45PM in minutes (1065 minutes)
    min_meeting_duration = 120  # minimum meeting duration in minutes

    # Compute the earliest arrival time at Presidio from Nob Hill
    earliest_arrival_presidio = arrival_time_nob_hill + travel_nobhill_to_presidio

    # The meeting with Robert cannot start before his availability.
    # Therefore, the optimal meeting start time is the maximum of your arrival at Presidio and Robert's start time.
    meeting_start = max(earliest_arrival_presidio, robert_available_start)
    
    # Calculate the meeting end time based on the minimum required duration.
    meeting_end = meeting_start + min_meeting_duration

    # Verify that the meeting ends before Robert leaves.
    if meeting_end > robert_available_end:
        result = {"error": "No valid meeting schedule can be found with the given constraints."}
    else:
        itinerary = []
        meeting_event = {
            "action": "meet",
            "location": "Presidio",
            "person": "Robert",
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        }
        itinerary.append(meeting_event)
        result = {"itinerary": itinerary}

    # Output the result as a JSON-formatted dictionary
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()