#!/usr/bin/env python3
import json

def minutes_to_timestr(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

def main():
    # Define travel times (in minutes) between locations
    travel_times = {
        ("North Beach", "Pacific Heights"): 8,
        ("North Beach", "Embarcadero"): 6,
        ("Pacific Heights", "North Beach"): 9,
        ("Pacific Heights", "Embarcadero"): 10,
        ("Embarcadero", "North Beach"): 5,
        ("Embarcadero", "Pacific Heights"): 11
    }
    
    # Arrival at North Beach at 9:00 (in minutes from midnight)
    nb_arrival = 9 * 60  # 540 minutes

    # Meeting constraints for Mark at Embarcadero
    mark_avail_start = 13 * 60         # 13:00 -> 780 minutes
    mark_avail_end = 17 * 60 + 45        # 17:45 -> 1065 minutes
    mark_min_duration = 120            # 120 minutes minimum meeting

    # Meeting constraints for Karen at Pacific Heights
    karen_avail_start = 18 * 60 + 45     # 18:45 -> 1125 minutes
    karen_avail_end = 20 * 60 + 15       # 20:15 -> 1215 minutes
    karen_min_duration = 90            # 90 minutes minimum meeting

    # For Mark, the meeting must fit within his available window.
    # The meeting can start any time t where mark_avail_start <= t <= mark_avail_end - mark_min_duration.
    # To optimize (minimize waiting at the meeting location later), we choose the latest feasible start.
    mark_meeting_start = mark_avail_end - mark_min_duration  # Latest start time: 1065 - 120 = 945 minutes (15:45)
    mark_meeting_end = mark_meeting_start + mark_min_duration  # Ends at 945 + 120 = 1065 minutes (17:45)
    
    # Calculate departure time from North Beach to Embarcadero
    travel_nb_to_emb = travel_times[("North Beach", "Embarcadero")]
    departure_from_nb = mark_meeting_start - travel_nb_to_emb
    if departure_from_nb < nb_arrival:
        print("Error: Not enough time to travel from North Beach to Embarcadero for Mark's meeting.")
        return

    # After meeting Mark, travel from Embarcadero to Pacific Heights for Karen
    travel_emb_to_ph = travel_times[("Embarcadero", "Pacific Heights")]
    arrival_at_ph = mark_meeting_end + travel_emb_to_ph

    # To meet Karen at her location when she is available, we schedule her meeting at the start of her availability.
    karen_meeting_start = karen_avail_start  # 1125 minutes (18:45)
    karen_meeting_end = karen_meeting_start + karen_min_duration  # 1125 + 90 = 1215 minutes (20:15)
    
    # Ensure Karen's meeting fits within her available window
    if karen_meeting_end > karen_avail_end:
        print("Error: Karen's meeting cannot be scheduled within her availability window.")
        return

    itinerary = [
        {
            "action": "meet",
            "location": "Embarcadero",
            "person": "Mark",
            "start_time": minutes_to_timestr(mark_meeting_start),
            "end_time": minutes_to_timestr(mark_meeting_end)
        },
        {
            "action": "meet",
            "location": "Pacific Heights",
            "person": "Karen",
            "start_time": minutes_to_timestr(karen_meeting_start),
            "end_time": minutes_to_timestr(karen_meeting_end)
        }
    ]
    
    schedule = {"itinerary": itinerary}
    print(json.dumps(schedule, indent=2))

if __name__ == "__main__":
    main()