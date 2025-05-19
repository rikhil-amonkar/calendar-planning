import json
from datetime import timedelta, datetime

def minutes_to_time(minutes):
    # Convert minutes from midnight into H:MM 24-hour format without leading zeros for hours.
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

def main():
    # Define travel times in minutes between locations.
    travel_times = {
        ("Financial District", "Fisherman's Wharf"): 10,
        ("Financial District", "Pacific Heights"): 13,
        ("Financial District", "Mission District"): 17,
        ("Fisherman's Wharf", "Financial District"): 11,
        ("Fisherman's Wharf", "Pacific Heights"): 12,
        ("Fisherman's Wharf", "Mission District"): 22,
        ("Pacific Heights", "Financial District"): 13,
        ("Pacific Heights", "Fisherman's Wharf"): 13,
        ("Pacific Heights", "Mission District"): 15,
        ("Mission District", "Financial District"): 17,
        ("Mission District", "Fisherman's Wharf"): 22,
        ("Mission District", "Pacific Heights"): 16,
    }
    
    # Meeting constraints and participant details.
    # Times in minutes from midnight.
    fd_arrival = 9 * 60  # 9:00
    # David: available at Fisherman's Wharf from 10:45 to 15:30, need min 15 minutes.
    david_location = "Fisherman's Wharf"
    david_start_available = 10 * 60 + 45  # 10:45
    david_end_available   = 15 * 60 + 30   # 15:30
    david_min_meeting = 15
    
    # Timothy: available at Pacific Heights from 9:00 to 15:30, need min 75 minutes.
    timothy_location = "Pacific Heights"
    timothy_start_available = 9 * 60  # 9:00
    timothy_end_available   = 15 * 60 + 30   # 15:30
    timothy_min_meeting = 75
    
    # Robert: available at Mission District from 12:15 to 19:45, need min 90 minutes.
    robert_location = "Mission District"
    robert_start_available = 12 * 60 + 15   # 12:15
    robert_end_available   = 19 * 60 + 45   # 19:45
    robert_min_meeting = 90

    itinerary = []
    
    # We plan the following route:
    # 1. Start at Financial District at 9:00. Travel to Pacific Heights to meet Timothy.
    # 2. Meet Timothy for at least 75 minutes.
    # 3. Travel from Pacific Heights to Fisherman's Wharf to meet David (available from 10:45).
    # 4. Meet David for at least 15 minutes.
    # 5. Travel from Fisherman's Wharf to Mission District to meet Robert (available from 12:15).
    # 6. Meet Robert for at least 90 minutes.
    
    # Starting point: Financial District at 9:00.
    current_location = "Financial District"
    current_time = fd_arrival  # minutes from midnight

    # 1. Travel from Financial District to Pacific Heights.
    travel_time = travel_times[(current_location, timothy_location)]
    current_time += travel_time  # arrival time at Pacific Heights
    timothy_meet_start = current_time  # start meeting Timothy at arrival.
    # Ensure meeting cannot start before participant's available time.
    if timothy_meet_start < timothy_start_available:
        timothy_meet_start = timothy_start_available
        current_time = timothy_meet_start

    # 2. Schedule meeting with Timothy.
    # Schedule exactly the minimum required meeting time.
    timothy_meet_duration = timothy_min_meeting
    timothy_meet_end = timothy_meet_start + timothy_meet_duration
    # Also ensure that the meeting does not go past Timothy's availability end.
    if timothy_meet_end > timothy_end_available:
        raise Exception("Cannot schedule meeting with Timothy within his availability window.")

    itinerary.append({
        "action": "meet",
        "location": timothy_location,
        "person": "Timothy",
        "start_time": minutes_to_time(timothy_meet_start),
        "end_time": minutes_to_time(timothy_meet_end)
    })

    # Update current time and location.
    current_time = timothy_meet_end
    current_location = timothy_location

    # 3. Travel from Pacific Heights to Fisherman's Wharf for David.
    travel_time = travel_times[(current_location, david_location)]
    current_time += travel_time
    # Wait if arriving before David's available start.
    if current_time < david_start_available:
        current_time = david_start_available
    david_meet_start = current_time

    # 4. Schedule meeting with David.
    david_meet_duration = david_min_meeting
    david_meet_end = david_meet_start + david_meet_duration
    if david_meet_end > david_end_available:
        raise Exception("Cannot schedule meeting with David within his availability window.")
    
    itinerary.append({
        "action": "meet",
        "location": david_location,
        "person": "David",
        "start_time": minutes_to_time(david_meet_start),
        "end_time": minutes_to_time(david_meet_end)
    })

    # Update current time and location.
    current_time = david_meet_end
    current_location = david_location

    # 5. Travel from Fisherman's Wharf to Mission District for Robert.
    travel_time = travel_times[(current_location, robert_location)]
    current_time += travel_time
    # Wait if arriving before Robert's available start.
    if current_time < robert_start_available:
        current_time = robert_start_available
    robert_meet_start = current_time

    # 6. Schedule meeting with Robert.
    robert_meet_duration = robert_min_meeting
    robert_meet_end = robert_meet_start + robert_meet_duration
    if robert_meet_end > robert_end_available:
        raise Exception("Cannot schedule meeting with Robert within his availability window.")

    itinerary.append({
        "action": "meet",
        "location": robert_location,
        "person": "Robert",
        "start_time": minutes_to_time(robert_meet_start),
        "end_time": minutes_to_time(robert_meet_end)
    })

    # Prepare the JSON result.
    schedule = {"itinerary": itinerary}
    print(json.dumps(schedule, indent=2))

if __name__ == "__main__":
    main()