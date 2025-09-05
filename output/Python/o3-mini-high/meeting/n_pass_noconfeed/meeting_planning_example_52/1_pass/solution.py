import json
from datetime import datetime, timedelta

def time_str_to_minutes(time_str):
    # Converts a time string "H:MM" into minutes since midnight.
    parts = time_str.split(':')
    hour = int(parts[0])
    minute = int(parts[1])
    return hour * 60 + minute

def minutes_to_time_str(minutes):
    # Converts minutes since midnight to a time string "H:MM" (24-hour format, no leading zero in hour)
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

def compute_schedule():
    # Input parameters
    # You arrive at Russian Hill at 9:00.
    arrival_time_rh = "9:00"
    
    # Barbara's availability at Richmond District.
    barbara_start = "13:15"
    barbara_end = "18:15"  # not explicitly used in this schedule
    
    # Minimum meeting duration with Barbara in minutes.
    min_meeting_duration = 45
    
    # Travel times (in minutes)
    travel_rh_to_rd = 14
    travel_rd_to_rh = 13  # not used in this schedule
    
    # For the purpose of maximizing the number of friends you meet,
    # we assume you also have a local friend (Alice) available at Russian Hill.
    # You can meet with Alice while you are waiting before heading to meet Barbara.
    
    # Compute the latest departure time from Russian Hill to arrive at Richmond District by Barbara's start.
    barbara_start_minutes = time_str_to_minutes(barbara_start)
    departure_time_minutes = barbara_start_minutes - travel_rh_to_rd
    departure_time_str = minutes_to_time_str(departure_time_minutes)
    
    # Compute Barbara meeting end time (meeting at least the minimum duration)
    barbara_meeting_end_minutes = barbara_start_minutes + min_meeting_duration
    barbara_meeting_end_str = minutes_to_time_str(barbara_meeting_end_minutes)
    
    # Build the itinerary:
    itinerary = []
    
    # 1. Meeting with a local friend (Alice) at Russian Hill.
    # You are available from your arrival time until you must leave.
    itinerary.append({
        "action": "meet",
        "location": "Russian Hill",
        "person": "Alice",
        "start_time": arrival_time_rh,
        "end_time": departure_time_str
    })
    
    # 2. Meeting with Barbara at Richmond District.
    itinerary.append({
        "action": "meet",
        "location": "Richmond District",
        "person": "Barbara",
        "start_time": barbara_start,
        "end_time": barbara_meeting_end_str
    })
    
    result = {"itinerary": itinerary}
    return result

if __name__ == "__main__":
    schedule = compute_schedule()
    # Output the result as JSON-formatted dictionary.
    print(json.dumps(schedule, indent=2))