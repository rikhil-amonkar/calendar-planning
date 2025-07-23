import json
from datetime import datetime, timedelta

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def format_time(dt):
    return dt.strftime("%-H:%M")

def calculate_schedule():
    # Travel times in minutes
    travel_times = {
        ('The Castro', 'Mission District'): 7,
        ('The Castro', 'Financial District'): 20,
        ('Mission District', 'The Castro'): 7,
        ('Mission District', 'Financial District'): 17,
        ('Financial District', 'The Castro'): 23,
        ('Financial District', 'Mission District'): 17
    }
    
    # Initial conditions
    current_location = 'The Castro'
    current_time = parse_time("9:00")
    
    # Meeting constraints
    laura_available_start = parse_time("12:15")
    laura_available_end = parse_time("19:45")
    laura_min_duration = timedelta(minutes=75)
    
    anthony_available_start = parse_time("12:30")
    anthony_available_end = parse_time("14:45")
    anthony_min_duration = timedelta(minutes=30)
    
    itinerary = []
    
    # Option 1: Meet Laura first, then Anthony
    option1_itinerary = []
    option1_valid = True
    
    # Travel to Mission District to meet Laura
    travel_duration = travel_times[(current_location, 'Mission District')]
    arrival_time = current_time + timedelta(minutes=travel_duration)
    
    # Calculate meeting window with Laura
    meeting_start = max(arrival_time, laura_available_start)
    meeting_end = meeting_start + laura_min_duration
    
    if meeting_end > laura_available_end:
        option1_valid = False
    else:
        option1_itinerary.append({
            "action": "meet",
            "location": "Mission District",
            "person": "Laura",
            "start_time": format_time(meeting_start),
            "end_time": format_time(meeting_end)
        })
        
        # Travel to Financial District to meet Anthony
        travel_duration = travel_times[('Mission District', 'Financial District')]
        arrival_time = meeting_end + timedelta(minutes=travel_duration)
        
        # Calculate meeting window with Anthony
        meeting_start = max(arrival_time, anthony_available_start)
        meeting_end = meeting_start + anthony_min_duration
        
        if meeting_end > anthony_available_end:
            option1_valid = False
        else:
            option1_itinerary.append({
                "action": "meet",
                "location": "Financial District",
                "person": "Anthony",
                "start_time": format_time(meeting_start),
                "end_time": format_time(meeting_end)
            })
    
    # Option 2: Meet Anthony first, then Laura
    option2_itinerary = []
    option2_valid = True
    
    # Travel to Financial District to meet Anthony
    travel_duration = travel_times[(current_location, 'Financial District')]
    arrival_time = current_time + timedelta(minutes=travel_duration)
    
    # Calculate meeting window with Anthony
    meeting_start = max(arrival_time, anthony_available_start)
    meeting_end = meeting_start + anthony_min_duration
    
    if meeting_end > anthony_available_end:
        option2_valid = False
    else:
        option2_itinerary.append({
            "action": "meet",
            "location": "Financial District",
            "person": "Anthony",
            "start_time": format_time(meeting_start),
            "end_time": format_time(meeting_end)
        })
        
        # Travel to Mission District to meet Laura
        travel_duration = travel_times[('Financial District', 'Mission District')]
        arrival_time = meeting_end + timedelta(minutes=travel_duration)
        
        # Calculate meeting window with Laura
        meeting_start = max(arrival_time, laura_available_start)
        meeting_end = meeting_start + laura_min_duration
        
        if meeting_end > laura_available_end:
            option2_valid = False
        else:
            option2_itinerary.append({
                "action": "meet",
                "location": "Mission District",
                "person": "Laura",
                "start_time": format_time(meeting_start),
                "end_time": format_time(meeting_end)
            })
    
    # Determine the best option
    if option1_valid and option2_valid:
        # Both options are valid, pick the one that meets Laura earlier
        if option1_itinerary[0]["person"] == "Laura":
            itinerary = option1_itinerary
        else:
            itinerary = option2_itinerary
    elif option1_valid:
        itinerary = option1_itinerary
    elif option2_valid:
        itinerary = option2_itinerary
    
    return {"itinerary": itinerary}

if __name__ == "__main__":
    schedule = calculate_schedule()
    print(json.dumps(schedule, indent=2))