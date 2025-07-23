import json

def time_to_minutes(time_str):
    parts = time_str.split(':')
    hour = int(parts[0])
    minute = int(parts[1]) if len(parts) > 1 else 0
    return hour * 60 + minute

def minutes_to_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

def main():
    # Input parameters
    start_time_str = "9:00"
    jessica_avail_start_str = "15:30"
    jessica_avail_end_str = "16:45"
    jessica_duration = 45
    carol_avail_start_str = "11:30"
    carol_avail_end_str = "15:00"
    carol_duration = 60
    richmond_to_marina = 9
    marina_to_pacific = 7

    # Convert times to minutes
    carol_start_avail = time_to_minutes(carol_avail_start_str)
    carol_end_avail = time_to_minutes(carol_avail_end_str)
    jessica_start_avail = time_to_minutes(jessica_avail_start_str)
    jessica_end_avail = time_to_minutes(jessica_avail_end_str)

    # Schedule Carol: latest possible meeting to minimize waiting at Pacific Heights
    carol_meeting_end = carol_end_avail
    carol_meeting_start = carol_meeting_end - carol_duration

    # Ensure Carol's meeting is within availability
    if carol_meeting_start < carol_start_avail:
        carol_meeting_start = carol_start_avail
        carol_meeting_end = carol_meeting_start + carol_duration

    # Travel to Pacific Heights after Carol
    arrive_pacific = carol_meeting_end + marina_to_pacific

    # Schedule Jessica: earliest possible after arrival or availability start
    jessica_meeting_start = max(arrive_pacific, jessica_start_avail)
    jessica_meeting_end = jessica_meeting_start + jessica_duration

    # Create itinerary
    itinerary = [
        {
            "action": "meet",
            "location": "Marina District",
            "person": "Carol",
            "start_time": minutes_to_time(carol_meeting_start),
            "end_time": minutes_to_time(carol_meeting_end)
        },
        {
            "action": "meet",
            "location": "Pacific Heights",
            "person": "Jessica",
            "start_time": minutes_to_time(jessica_meeting_start),
            "end_time": minutes_to_time(jessica_meeting_end)
        }
    ]

    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()