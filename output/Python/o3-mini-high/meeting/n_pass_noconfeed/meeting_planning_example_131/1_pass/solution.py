import json

def minutes_to_time_str(minutes):
    # Convert minutes since midnight to H:MM format (without leading zero for hour)
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

def main():
    # Travel times in minutes between locations
    travel_times = {
        ("Pacific Heights", "Presidio"): 11,
        ("Pacific Heights", "Marina District"): 6,
        ("Presidio", "Pacific Heights"): 11,
        ("Presidio", "Marina District"): 10,
        ("Marina District", "Pacific Heights"): 7,
        ("Marina District", "Presidio"): 10
    }
    
    # Starting point and arrival time at Pacific Heights (9:00AM)
    start_PH = 9 * 60  # 9:00 AM in minutes since midnight (540)
    
    # Jason's meeting constraints (at Presidio)
    jason_available_start = 10 * 60         # 10:00AM -> 600 minutes
    jason_available_end = 16 * 60 + 15        # 4:15PM -> 975 minutes
    jason_min_duration = 90                   # minimum 90 minutes meeting
    
    # Kenneth's meeting constraints (at Marina District)
    kenneth_available_start = 15 * 60 + 30    # 3:30PM -> 930 minutes
    kenneth_available_end = 16 * 60 + 45       # 4:45PM -> 1005 minutes
    kenneth_min_duration = 45                 # minimum 45 minutes meeting

    # Calculate meeting with Jason:
    # Travel from Pacific Heights to Presidio.
    travel_PH_to_Presidio = travel_times[("Pacific Heights", "Presidio")]
    arrival_at_presidio = start_PH + travel_PH_to_Presidio
    # Jason is available starting from 10:00AM, so meeting starts at the later of arrival time or his available time.
    jason_meeting_start = max(arrival_at_presidio, jason_available_start)
    jason_meeting_end = jason_meeting_start + jason_min_duration
    if jason_meeting_end > jason_available_end:
        raise ValueError("Unable to schedule required meeting duration with Jason within his availability.")
    
    # Calculate meeting with Kenneth:
    # After finishing with Jason at Presidio, plan travel to Marina District.
    travel_Presidio_to_Marina = travel_times[("Presidio", "Marina District")]
    # To start meeting Kenneth at his available start time (3:30PM), you must leave Presidio by:
    required_departure_for_kenneth = kenneth_available_start - travel_Presidio_to_Marina
    # You finish Jason at jason_meeting_end; if that's earlier than required departure,
    # wait until required departure time.
    departure_from_presidio = max(jason_meeting_end, required_departure_for_kenneth)
    arrival_at_marina = departure_from_presidio + travel_Presidio_to_Marina
    # Meeting with Kenneth can start when he is available and you've arrived.
    kenneth_meeting_start = max(arrival_at_marina, kenneth_available_start)
    kenneth_meeting_end = kenneth_meeting_start + kenneth_min_duration
    if kenneth_meeting_end > kenneth_available_end:
        raise ValueError("Unable to schedule required meeting duration with Kenneth within his availability.")

    # Define the itinerary based on computed meeting times
    itinerary = [
        {
            "action": "meet",
            "location": "Presidio",
            "person": "Jason",
            "start_time": minutes_to_time_str(jason_meeting_start),
            "end_time": minutes_to_time_str(jason_meeting_end)
        },
        {
            "action": "meet",
            "location": "Marina District",
            "person": "Kenneth",
            "start_time": minutes_to_time_str(kenneth_meeting_start),
            "end_time": minutes_to_time_str(kenneth_meeting_end)
        }
    ]
    
    schedule = {"itinerary": itinerary}
    print(json.dumps(schedule, indent=2))

if __name__ == "__main__":
    main()