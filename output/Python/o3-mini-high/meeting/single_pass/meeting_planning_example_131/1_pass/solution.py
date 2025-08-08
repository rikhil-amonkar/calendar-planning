#!/usr/bin/env python3
import json

def minutes_to_time_str(minutes):
    # Converts minutes since midnight to "H:MM" in 24-hour format with no leading zero for hours.
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

def compute_schedule():
    # Travel times in minutes (as given)
    travel_times = {
        ("Pacific Heights", "Presidio"): 11,
        ("Pacific Heights", "Marina District"): 6,
        ("Presidio", "Pacific Heights"): 11,
        ("Presidio", "Marina District"): 10,
        ("Marina District", "Pacific Heights"): 7,
        ("Marina District", "Presidio"): 10
    }
    
    # Constraint times in minutes since midnight
    # Arrival at Pacific Heights at 9:00
    ph_arrival = 9 * 60  # 540
    
    # Jason's availability at Presidio: 10:00 to 16:15
    jason_available_start = 10 * 60       # 600
    jason_available_end   = 16 * 60 + 15    # 975
    jason_min_meeting_duration = 90       # minutes
    
    # Kenneth's availability at Marina District: 15:30 to 16:45
    kenneth_available_start = 15 * 60 + 30  # 930
    kenneth_available_end   = 16 * 60 + 45    # 1005
    kenneth_min_meeting_duration = 45      # minutes
    
    # We consider two candidate schedules.
    #
    # Option 1: Depart Pacific Heights immediately at 9:00:
    #   - Depart PH at 9:00, travel to Presidio (11 min) → arrive 9:11.
    #   - Wait until Jason available start (10:00). Meeting with Jason 10:00 to 10:00+90 = 11:30.
    #   - Immediately depart Presidio to Marina District (10 min) → arrive at 11:40.
    #   - Wait until Kenneth is available (15:30) and meet from 15:30 to 15:30+45 = 16:15.
    #
    # Option 2 (optimal): Time the meetings to avoid waiting in the middle of the day:
    #   - Stay at Pacific Heights until it's time to leave, so that travel and meetings are contiguous.
    #   - To catch Kenneth on time, we need to arrive at Marina District exactly at Kenneth's available start (15:30).
    #   - The travel time from Presidio to Marina is 10 minutes, so we must finish Jason's meeting by 15:20.
    #   - With a 90-minute meeting with Jason, the meeting must start at 15:20 - 90 = 13:50.
    #   - To be at Presidio by 13:50, leave Pacific Heights at 13:50 - 11 = 13:39.
    #   - Then, meet Jason at Presidio from 13:50 to 15:20.
    #   - Depart Presidio at 15:20; after 10 minutes travel arrive at Marina at 15:30.
    #   - Meet Kenneth at Marina District from 15:30 to 15:30+45 = 16:15.
    
    # Calculate Option 1 timings:
    opt1_ph_departure = ph_arrival  # depart immediately at 9:00
    opt1_arrival_presidio = opt1_ph_departure + travel_times[("Pacific Heights", "Presidio")]
    # Wait until Jason available start:
    opt1_jason_meeting_start = max(opt1_arrival_presidio, jason_available_start)
    opt1_jason_meeting_end = opt1_jason_meeting_start + jason_min_meeting_duration
    
    opt1_depart_presidio = opt1_jason_meeting_end
    opt1_arrival_marina = opt1_depart_presidio + travel_times[("Presidio", "Marina District")]
    opt1_kenneth_meeting_start = max(opt1_arrival_marina, kenneth_available_start)
    opt1_kenneth_meeting_end = opt1_kenneth_meeting_start + kenneth_min_meeting_duration

    # For Option 1, waiting time at non-home locations:
    # Waiting at Presidio before Jason meeting = opt1_jason_meeting_start - opt1_arrival_presidio
    # Waiting at Marina before Kenneth meeting = opt1_kenneth_meeting_start - opt1_arrival_marina
    opt1_wait_presidio = opt1_jason_meeting_start - opt1_arrival_presidio
    opt1_wait_marina = opt1_kenneth_meeting_start - opt1_arrival_marina
    # We assume waiting while away from home (PH) is less ideal, and we weight it more.
    opt1_penalty = (opt1_wait_presidio + opt1_wait_marina) * 2

    # Calculate Option 2 timings (optimal scheduling):
    # Determine latest possible Jason meeting such that Kenneth meeting is not missed:
    # Kenneth meeting must start at kenneth_available_start = 15:30 (930 minutes)
    # To arrive then from Presidio, travel time = 10 minutes, so must leave Presidio by 15:20 (920 minutes)
    # Meeting with Jason takes 90 minutes, so must start at 920 - 90 = 830 minutes (13:50)
    opt2_jason_meeting_start = 13 * 60 + 50        # 830 minutes = 13:50
    opt2_jason_meeting_end = opt2_jason_meeting_start + jason_min_meeting_duration  # 830+90 = 920 (15:20)
    # To be at Presidio by 13:50, leave PH at 13:50 minus travel time of 11 minutes:
    opt2_ph_departure = opt2_jason_meeting_start - travel_times[("Pacific Heights", "Presidio")]  # 830 - 11 = 819 (13:39)
    opt2_arrival_presidio = opt2_ph_departure + travel_times[("Pacific Heights", "Presidio")]  # should be 830 exactly
    # Then after Jason meeting ends at 920, travel to Marina:
    opt2_depart_presidio = opt2_jason_meeting_end   # 920 (15:20)
    opt2_arrival_marina = opt2_depart_presidio + travel_times[("Presidio", "Marina District")]  # 920+10 = 930 (15:30)
    opt2_kenneth_meeting_start = kenneth_available_start  # 930 (15:30)
    opt2_kenneth_meeting_end = opt2_kenneth_meeting_start + kenneth_min_meeting_duration  # 930+45 = 975 (16:15)
    
    # In Option 2, waiting happens at home (PH) until departure.
    opt2_wait_home = opt2_ph_departure - ph_arrival  # waiting at PH
    # We'll assign a lower penalty weight for waiting at home (weight=1) than away from a friend's location.
    opt2_penalty = opt2_wait_home * 1

    # Choose the option with the lower penalty.
    if opt2_penalty <= opt1_penalty:
        # Use Option 2
        schedule = {
            "PH_wait_until": minutes_to_time_str(opt2_ph_departure),  # when leaving home
            "ph_departure": minutes_to_time_str(opt2_ph_departure),
            "arrival_presidio": minutes_to_time_str(opt2_arrival_presidio),
            "jason_meeting_start": minutes_to_time_str(opt2_jason_meeting_start),
            "jason_meeting_end": minutes_to_time_str(opt2_jason_meeting_end),
            "depart_presidio": minutes_to_time_str(opt2_depart_presidio),
            "arrival_marina": minutes_to_time_str(opt2_arrival_marina),
            "kenneth_meeting_start": minutes_to_time_str(opt2_kenneth_meeting_start),
            "kenneth_meeting_end": minutes_to_time_str(opt2_kenneth_meeting_end)
        }
        # Build itinerary with only the meeting actions.
        itinerary = [
            {
                "action": "meet",
                "location": "Presidio",
                "person": "Jason",
                "start_time": minutes_to_time_str(opt2_jason_meeting_start),
                "end_time": minutes_to_time_str(opt2_jason_meeting_end)
            },
            {
                "action": "meet",
                "location": "Marina District",
                "person": "Kenneth",
                "start_time": minutes_to_time_str(opt2_kenneth_meeting_start),
                "end_time": minutes_to_time_str(opt2_kenneth_meeting_end)
            }
        ]
    else:
        # Use Option 1 if it were better.
        schedule = {
            "ph_departure": minutes_to_time_str(opt1_ph_departure),
            "arrival_presidio": minutes_to_time_str(opt1_arrival_presidio),
            "jason_meeting_start": minutes_to_time_str(opt1_jason_meeting_start),
            "jason_meeting_end": minutes_to_time_str(opt1_jason_meeting_end),
            "depart_presidio": minutes_to_time_str(opt1_depart_presidio),
            "arrival_marina": minutes_to_time_str(opt1_arrival_marina),
            "kenneth_meeting_start": minutes_to_time_str(opt1_kenneth_meeting_start),
            "kenneth_meeting_end": minutes_to_time_str(opt1_kenneth_meeting_end)
        }
        itinerary = [
            {
                "action": "meet",
                "location": "Presidio",
                "person": "Jason",
                "start_time": minutes_to_time_str(opt1_jason_meeting_start),
                "end_time": minutes_to_time_str(opt1_jason_meeting_end)
            },
            {
                "action": "meet",
                "location": "Marina District",
                "person": "Kenneth",
                "start_time": minutes_to_time_str(opt1_kenneth_meeting_start),
                "end_time": minutes_to_time_str(opt1_kenneth_meeting_end)
            }
        ]
    
    # For our optimization, Option 2 is better.
    result = {"itinerary": itinerary}
    return result

def main():
    schedule_result = compute_schedule()
    print(json.dumps(schedule_result, indent=2))

if __name__ == "__main__":
    main()