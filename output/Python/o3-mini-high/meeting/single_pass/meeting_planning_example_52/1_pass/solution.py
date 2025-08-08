#!/usr/bin/env python3
import json

def minutes_to_time_str(total_minutes):
    hours = total_minutes // 60
    minutes = total_minutes % 60
    # Format the time as H:MM, ensuring no leading zero for hour
    return f"{hours}:{minutes:02d}"

def main():
    # Input parameters
    start_time_str = "9:00"  # Arrival at Russian Hill
    # Convert start time to minutes from midnight (9:00 AM -> 9*60 = 540)
    start_minutes = 9 * 60  # 540 minutes

    # Travel times in minutes
    travel_rh_to_rd = 14  # Russian Hill to Richmond District
    travel_rd_to_rh = 13  # Richmond District to Russian Hill

    # Barbara's availability and meeting constraint
    barbara_start_str = "13:15"
    barbara_end_str = "18:15"
    # Convert Barbara's times to minutes from midnight
    barbara_start_minutes = 13 * 60 + 15  # 13:15 -> 795 minutes
    barbara_end_minutes = 18 * 60 + 15      # 18:15 -> 1095 minutes

    min_meeting_duration = 45  # Minimum meeting duration in minutes

    # Compute optimal departure time from Russian Hill so that you arrive by Barbara's start time.
    # Arrival time at Richmond District = departure time + travel_rh_to_rd
    # To arrive at 13:15, departure time must be barbara_start_minutes - travel_rh_to_rd.
    departure_minutes = barbara_start_minutes - travel_rh_to_rd

    # Arrival time at Richmond District from Russian Hill
    arrival_minutes = departure_minutes + travel_rh_to_rd

    # The meeting can start at Barbara's available time (or later if arrival is later)
    meeting_start_minutes = max(arrival_minutes, barbara_start_minutes)
    # Schedule the meeting for the minimum required duration
    meeting_end_minutes = meeting_start_minutes + min_meeting_duration

    # Verify that the meeting ends within Barbara's availability window.
    if meeting_end_minutes > barbara_end_minutes:
        meeting_end_minutes = barbara_end_minutes

    itinerary = []
    # Create the meeting event with Barbara
    meeting_event = {
        "action": "meet",
        "location": "Richmond District",
        "person": "Barbara",
        "start_time": minutes_to_time_str(meeting_start_minutes),
        "end_time": minutes_to_time_str(meeting_end_minutes)
    }
    itinerary.append(meeting_event)

    schedule = {"itinerary": itinerary}

    # Output the schedule as a JSON-formatted dictionary
    print(json.dumps(schedule))

if __name__ == "__main__":
    main()