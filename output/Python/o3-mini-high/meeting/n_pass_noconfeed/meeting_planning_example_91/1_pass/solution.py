import json
from datetime import datetime, timedelta

def minutes_to_time_str(dt):
    # Format time as H:MM (no leading zero for hour)
    return f"{dt.hour}:{dt.minute:02}"

def main():
    # Input parameters
    arrival_str = "9:00"                   # Arrival time at Russian Hill (HH:MM 24-hour)
    daniel_start_str = "19:00"             # Daniel available start at Richmond District
    daniel_end_str = "20:15"               # Daniel available end at Richmond District
    required_meeting_duration = 75         # Minimum meeting duration with Daniel in minutes
    travel_rh_to_rd = 14                   # Travel time from Russian Hill to Richmond District (in minutes)
    travel_rd_to_rh = 13                   # Travel time from Richmond District to Russian Hill (in minutes)

    # Use a base date for all time computations
    base_date = "2000-01-01"
    time_format = "%Y-%m-%d %H:%M"
    
    arrival_time = datetime.strptime(f"{base_date} {arrival_str}", time_format)
    daniel_start = datetime.strptime(f"{base_date} {daniel_start_str}", time_format)
    daniel_end = datetime.strptime(f"{base_date} {daniel_end_str}", time_format)
    
    # Check if Daniel's available window meets the required meeting duration
    available_duration = (daniel_end - daniel_start).total_seconds() / 60
    if available_duration < required_meeting_duration:
        result = {"error": "Daniel's availability does not meet the required meeting duration."}
        print(json.dumps(result, indent=2))
        return

    # Compute the departure time from Russian Hill so as to arrive by Daniel's start time
    # You must leave Russian Hill travel_rh_to_rd minutes prior to daniel_start.
    departure_from_rh = daniel_start - timedelta(minutes=travel_rh_to_rd)
    
    # (For optimization purposes, one might consider scheduling additional meetings at Russian Hill before departure.
    #  In this scenario, the only specific friend constraint provided is Daniel's.)
    
    # Set Daniel's meeting time.
    # To meet Daniel for at least required_meeting_duration minutes (75 minutes),
    # we schedule the meeting starting at his available start time.
    meeting_start = daniel_start
    meeting_end = daniel_end  # This exactly gives a 75-minute meeting.

    # Build the itinerary as a list of meeting events.
    itinerary = {
        "itinerary": [
            {
                "action": "meet",
                "location": "Richmond District",
                "person": "Daniel",
                "start_time": minutes_to_time_str(meeting_start),
                "end_time": minutes_to_time_str(meeting_end)
            }
        ]
    }

    # Output the result as a JSON formatted string
    print(json.dumps(itinerary, indent=2))

if __name__ == "__main__":
    main()