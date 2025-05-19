#!/usr/bin/env python3
import json
from datetime import datetime, timedelta

def minutes_to_time_str(total_minutes):
    # Convert minutes since midnight to H:MM format with no leading zero for hour.
    hours = total_minutes // 60
    minutes = total_minutes % 60
    return f"{hours}:{minutes:02d}"

def add_minutes(time_str, mins):
    # time_str expected in H:MM, convert to minutes since midnight, add mins, and convert back.
    hours, minutes = map(int, time_str.split(':'))
    total = hours * 60 + minutes + mins
    return minutes_to_time_str(total)

def compute_schedule():
    # Define the travel times (in minutes)
    travel_times = {
        ("North Beach", "Union Square"): 7,
        ("North Beach", "Russian Hill"): 4,
        ("Union Square", "North Beach"): 10,
        ("Union Square", "Russian Hill"): 13,
        ("Russian Hill", "North Beach"): 5,
        ("Russian Hill", "Union Square"): 11
    }
    
    # Constraints and fixed parameters
    arrival_location = "North Beach"
    arrival_time = "9:00"  # 9:00 AM arrival at North Beach

    # Emily constraints
    emily_location = "Union Square"
    emily_avail_start = "16:00"  # 4:00 PM
    emily_avail_end   = "17:15"  # 5:15 PM
    emily_min_duration = 45   # minutes

    # Margaret constraints
    margaret_location = "Russian Hill"
    margaret_avail_start = "19:00"  # 7:00 PM
    margaret_avail_end   = "21:00"  # 9:00 PM
    margaret_min_duration = 120  # minutes

    # Calculate departure from North Beach to meet Emily
    # We need to arrive at Emily's location at or just after her available start.
    # Travel time from North Beach to Union Square is:
    travel_nb_to_us = travel_times[(arrival_location, emily_location)]
    # To arrive at exactly 16:00, we leave North Beach at:
    # Convert 16:00 to minutes
    emily_start_minutes = int(emily_avail_start.split(':')[0]) * 60 + int(emily_avail_start.split(':')[1])
    departure_from_nb_minutes = emily_start_minutes - travel_nb_to_us
    departure_from_nb = minutes_to_time_str(departure_from_nb_minutes)
    
    # Meeting with Emily: start exactly at 16:00 and meet for 45 minutes.
    emily_meeting_start = emily_avail_start
    emily_meeting_end = add_minutes(emily_meeting_start, emily_min_duration)
    
    # After meeting Emily, travel from Union Square to Russian Hill.
    travel_us_to_rh = travel_times[(emily_location, margaret_location)]
    # Calculate arrival at Russian Hill if we left immediately after Emily meeting:
    arrival_rh_if_direct = add_minutes(emily_meeting_end, travel_us_to_rh)
    # But Margaret is only available starting at 19:00.
    # So the meeting with Margaret will start at max(arrival time, margaret_avail_start)
    # In our case, arrival_rh_if_direct is likely before 19:00.
    margaret_meeting_start = margaret_avail_start
    margaret_meeting_end = add_minutes(margaret_meeting_start, margaret_min_duration)
    
    # Check if this schedule respects Margaret's availability window.
    # margaret_meeting_end must be <= margaret_avail_end.
    # Convert times to minutes to check.
    margaret_meeting_end_minutes = int(margaret_meeting_end.split(':')[0]) * 60 + int(margaret_meeting_end.split(':')[1])
    margaret_avail_end_minutes = int(margaret_avail_end.split(':')[0]) * 60 + int(margaret_avail_end.split(':')[1])
    
    if margaret_meeting_end_minutes > margaret_avail_end_minutes:
        raise ValueError("Cannot schedule Margaret's meeting within her availability window given travel constraints.")
    
    # Build itinerary as list of meeting actions.
    itinerary = []
    
    # Meeting with Emily at Union Square.
    itinerary.append({
        "action": "meet",
        "location": emily_location,
        "person": "Emily",
        "start_time": emily_meeting_start,
        "end_time": emily_meeting_end
    })
    
    # Meeting with Margaret at Russian Hill.
    itinerary.append({
        "action": "meet",
        "location": margaret_location,
        "person": "Margaret",
        "start_time": margaret_meeting_start,
        "end_time": margaret_meeting_end
    })
    
    # Create final schedule JSON dictionary.
    schedule = {
        "itinerary": itinerary
    }
    
    return schedule

if __name__ == '__main__':
    schedule = compute_schedule()
    print(json.dumps(schedule, indent=2))