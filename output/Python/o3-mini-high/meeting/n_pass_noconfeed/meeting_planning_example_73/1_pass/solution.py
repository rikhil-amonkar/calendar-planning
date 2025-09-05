import json

def minutes_to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    # Input parameters (all times in minutes from midnight)
    arrival_time_russian_hill = 9 * 60         # 9:00 AM = 540 minutes
    barbara_available_start = 7 * 60 + 15        # 7:15 AM = 435 minutes
    barbara_available_end = 22 * 60              # 22:00 = 1320 minutes
    min_meeting_duration = 60                    # Minimum meeting duration in minutes

    # Travel times in minutes
    travel_time_rh_to_ph = 7                     # Russian Hill to Pacific Heights
    travel_time_ph_to_rh = 7                     # Pacific Heights to Russian Hill (if needed later)

    # Compute the earliest meeting start time at Pacific Heights.
    # You depart Russian Hill at arrival time, add travel time.
    meeting_start_time = arrival_time_russian_hill + travel_time_rh_to_ph

    # If arrival at Pacific Heights is before Barbara is available, adjust the meeting start time.
    if meeting_start_time < barbara_available_start:
        meeting_start_time = barbara_available_start

    # Calculate the meeting end time ensuring the meeting lasts at least the minimum duration.
    meeting_end_time = meeting_start_time + min_meeting_duration

    # Ensure that the meeting ends before Barbara leaves.
    if meeting_end_time > barbara_available_end:
        raise ValueError("Unable to schedule a meeting within Barbara's available hours.")

    itinerary = [
        {
            "action": "meet",
            "location": "Pacific Heights",
            "person": "Barbara",
            "start_time": minutes_to_time_str(meeting_start_time),
            "end_time": minutes_to_time_str(meeting_end_time)
        }
    ]

    schedule = {"itinerary": itinerary}
    print(json.dumps(schedule, indent=2))

if __name__ == "__main__":
    main()