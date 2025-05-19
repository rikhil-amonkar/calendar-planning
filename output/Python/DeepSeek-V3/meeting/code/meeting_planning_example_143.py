import json
from datetime import datetime, timedelta

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def format_time(dt):
    return dt.strftime("%-H:%M")

def calculate_schedule():
    # Input parameters
    travel_times = {
        ("North Beach", "Pacific Heights"): 8,
        ("North Beach", "Embarcadero"): 6,
        ("Pacific Heights", "North Beach"): 9,
        ("Pacific Heights", "Embarcadero"): 10,
        ("Embarcadero", "North Beach"): 5,
        ("Embarcadero", "Pacific Heights"): 11
    }
    
    current_location = "North Beach"
    current_time = parse_time("9:00")
    
    karen_available_start = parse_time("18:45")
    karen_available_end = parse_time("20:15")
    karen_min_duration = timedelta(minutes=90)
    
    mark_available_start = parse_time("13:00")
    mark_available_end = parse_time("17:45")
    mark_min_duration = timedelta(minutes=120)
    
    itinerary = []
    
    # Try to meet Mark first
    # Travel to Embarcadero
    travel_time = travel_times[(current_location, "Embarcadero")]
    arrival_at_mark = current_time + timedelta(minutes=travel_time)
    
    # Calculate meeting window with Mark
    meeting_start_mark = max(arrival_at_mark, mark_available_start)
    meeting_end_mark = min(meeting_start_mark + mark_min_duration, mark_available_end)
    
    if meeting_end_mark - meeting_start_mark >= mark_min_duration:
        # Can meet Mark
        itinerary.append({
            "action": "meet",
            "location": "Embarcadero",
            "person": "Mark",
            "start_time": format_time(meeting_start_mark),
            "end_time": format_time(meeting_end_mark)
        })
        
        # Travel to Pacific Heights for Karen
        travel_time_to_karen = travel_times[("Embarcadero", "Pacific Heights")]
        arrival_at_karen = meeting_end_mark + timedelta(minutes=travel_time_to_karen)
        
        # Calculate meeting window with Karen
        meeting_start_karen = max(arrival_at_karen, karen_available_start)
        meeting_end_karen = min(meeting_start_karen + karen_min_duration, karen_available_end)
        
        if meeting_end_karen - meeting_start_karen >= karen_min_duration:
            itinerary.append({
                "action": "meet",
                "location": "Pacific Heights",
                "person": "Karen",
                "start_time": format_time(meeting_start_karen),
                "end_time": format_time(meeting_end_karen)
            })
        else:
            # Can't meet Karen after Mark, try meeting Karen first
            itinerary = []
            
            # Travel to Pacific Heights first
            travel_time_to_karen = travel_times[(current_location, "Pacific Heights")]
            arrival_at_karen = current_time + timedelta(minutes=travel_time_to_karen)
            
            # Karen isn't available until 18:45, so this won't work
            # So we must meet Mark first and see if we can meet Karen after
            # If not, try to meet only one person
            # Let's try meeting only Karen
            arrival_at_karen = max(arrival_at_karen, karen_available_start)
            meeting_end_karen = min(arrival_at_karen + karen_min_duration, karen_available_end)
            
            if meeting_end_karen - arrival_at_karen >= karen_min_duration:
                itinerary.append({
                    "action": "meet",
                    "location": "Pacific Heights",
                    "person": "Karen",
                    "start_time": format_time(arrival_at_karen),
                    "end_time": format_time(meeting_end_karen)
                })
    else:
        # Can't meet Mark first, try meeting Karen first
        # Travel to Pacific Heights
        travel_time_to_karen = travel_times[(current_location, "Pacific Heights")]
        arrival_at_karen = current_time + timedelta(minutes=travel_time_to_karen)
        
        # Karen isn't available until 18:45, so this won't work
        # So the only option is to meet Mark with adjusted times or meet only Karen
        
        # Try to meet Mark with adjusted times
        meeting_start_mark = mark_available_start
        meeting_end_mark = min(meeting_start_mark + mark_min_duration, mark_available_end)
        
        if meeting_end_mark - meeting_start_mark >= mark_min_duration:
            # Can meet Mark
            travel_time_to_mark = travel_times[(current_location, "Embarcadero")]
            arrival_at_mark = current_time + timedelta(minutes=travel_time_to_mark)
            
            if arrival_at_mark <= meeting_start_mark:
                itinerary.append({
                    "action": "meet",
                    "location": "Embarcadero",
                    "person": "Mark",
                    "start_time": format_time(meeting_start_mark),
                    "end_time": format_time(meeting_end_mark)
                })
                
                # Check if we can meet Karen after
                travel_time_to_karen = travel_times[("Embarcadero", "Pacific Heights")]
                arrival_at_karen = meeting_end_mark + timedelta(minutes=travel_time_to_karen)
                
                meeting_start_karen = max(arrival_at_karen, karen_available_start)
                meeting_end_karen = min(meeting_start_karen + karen_min_duration, karen_available_end)
                
                if meeting_end_karen - meeting_start_karen >= karen_min_duration:
                    itinerary.append({
                        "action": "meet",
                        "location": "Pacific Heights",
                        "person": "Karen",
                        "start_time": format_time(meeting_start_karen),
                        "end_time": format_time(meeting_end_karen)
                    })
    
    # If we still have no itinerary, try meeting just one person
    if not itinerary:
        # Try meeting Mark
        travel_time_to_mark = travel_times[(current_location, "Embarcadero")]
        arrival_at_mark = current_time + timedelta(minutes=travel_time_to_mark)
        
        meeting_start_mark = max(arrival_at_mark, mark_available_start)
        meeting_end_mark = min(meeting_start_mark + mark_min_duration, mark_available_end)
        
        if meeting_end_mark - meeting_start_mark >= mark_min_duration:
            itinerary.append({
                "action": "meet",
                "location": "Embarcadero",
                "person": "Mark",
                "start_time": format_time(meeting_start_mark),
                "end_time": format_time(meeting_end_mark)
            })
        else:
            # Try meeting Karen
            travel_time_to_karen = travel_times[(current_location, "Pacific Heights")]
            arrival_at_karen = current_time + timedelta(minutes=travel_time_to_karen)
            
            meeting_start_karen = max(arrival_at_karen, karen_available_start)
            meeting_end_karen = min(meeting_start_karen + karen_min_duration, karen_available_end)
            
            if meeting_end_karen - meeting_start_karen >= karen_min_duration:
                itinerary.append({
                    "action": "meet",
                    "location": "Pacific Heights",
                    "person": "Karen",
                    "start_time": format_time(meeting_start_karen),
                    "end_time": format_time(meeting_end_karen)
                })
    
    return {"itinerary": itinerary}

if __name__ == "__main__":
    schedule = calculate_schedule()
    print(json.dumps(schedule, indent=2))