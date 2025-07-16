import json
from datetime import datetime, timedelta

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def format_time(dt):
    return dt.strftime("%-H:%M")

def calculate_schedule():
    # Input parameters
    travel_times = {
        ('Financial District', 'Chinatown'): 5,
        ('Financial District', 'Golden Gate Park'): 23,
        ('Chinatown', 'Financial District'): 5,
        ('Chinatown', 'Golden Gate Park'): 23,
        ('Golden Gate Park', 'Financial District'): 26,
        ('Golden Gate Park', 'Chinatown'): 23,
    }
    
    current_location = "Financial District"
    current_time = parse_time("9:00")
    
    kenneth_available_start = parse_time("12:00")
    kenneth_available_end = parse_time("15:00")
    kenneth_min_duration = timedelta(minutes=90)
    
    barbara_available_start = parse_time("8:15")
    barbara_available_end = parse_time("19:00")
    barbara_min_duration = timedelta(minutes=45)
    
    itinerary = []
    
    # Try to meet Kenneth first
    # Option 1: Go to Chinatown first
    travel_to_chinatown = travel_times[(current_location, 'Chinatown')]
    arrive_chinatown = current_time + timedelta(minutes=travel_to_chinatown)
    
    # Calculate possible meeting time with Kenneth
    kenneth_meet_start = max(arrive_chinatown, kenneth_available_start)
    kenneth_meet_end = kenneth_meet_start + kenneth_min_duration
    
    if kenneth_meet_end <= kenneth_available_end:
        # Can meet Kenneth
        itinerary.append({
            "action": "meet",
            "location": "Chinatown",
            "person": "Kenneth",
            "start_time": format_time(kenneth_meet_start),
            "end_time": format_time(kenneth_meet_end)
        })
        
        # Then go to Golden Gate Park to meet Barbara
        travel_to_ggp = travel_times[('Chinatown', 'Golden Gate Park')]
        arrive_ggp = kenneth_meet_end + timedelta(minutes=travel_to_ggp)
        
        barbara_meet_start = max(arrive_ggp, barbara_available_start)
        barbara_meet_end = barbara_meet_start + barbara_min_duration
        
        if barbara_meet_end <= barbara_available_end:
            itinerary.append({
                "action": "meet",
                "location": "Golden Gate Park",
                "person": "Barbara",
                "start_time": format_time(barbara_meet_start),
                "end_time": format_time(barbara_meet_end)
            })
            return {"itinerary": itinerary}
    
    # Option 2: Go to Golden Gate Park first
    travel_to_ggp = travel_times[(current_location, 'Golden Gate Park')]
    arrive_ggp = current_time + timedelta(minutes=travel_to_ggp)
    
    # Calculate possible meeting time with Barbara
    barbara_meet_start = max(arrive_ggp, barbara_available_start)
    barbara_meet_end = barbara_meet_start + barbara_min_duration
    
    if barbara_meet_end <= barbara_available_end:
        itinerary.append({
            "action": "meet",
            "location": "Golden Gate Park",
            "person": "Barbara",
            "start_time": format_time(barbara_meet_start),
            "end_time": format_time(barbara_meet_end)
        })
        
        # Then go to Chinatown to meet Kenneth
        travel_to_chinatown = travel_times[('Golden Gate Park', 'Chinatown')]
        arrive_chinatown = barbara_meet_end + timedelta(minutes=travel_to_chinatown)
        
        kenneth_meet_start = max(arrive_chinatown, kenneth_available_start)
        kenneth_meet_end = kenneth_meet_start + kenneth_min_duration
        
        if kenneth_meet_end <= kenneth_available_end:
            itinerary.append({
                "action": "meet",
                "location": "Chinatown",
                "person": "Kenneth",
                "start_time": format_time(kenneth_meet_start),
                "end_time": format_time(kenneth_meet_end)
            })
            return {"itinerary": itinerary}
    
    # If neither option works, try to meet just one person
    itinerary = []
    
    # Try to meet Kenneth
    travel_to_chinatown = travel_times[(current_location, 'Chinatown')]
    arrive_chinatown = current_time + timedelta(minutes=travel_to_chinatown)
    kenneth_meet_start = max(arrive_chinatown, kenneth_available_start)
    kenneth_meet_end = kenneth_meet_start + kenneth_min_duration
    
    if kenneth_meet_end <= kenneth_available_end:
        itinerary.append({
            "action": "meet",
            "location": "Chinatown",
            "person": "Kenneth",
            "start_time": format_time(kenneth_meet_start),
            "end_time": format_time(kenneth_meet_end)
        })
        return {"itinerary": itinerary}
    
    # Try to meet Barbara
    travel_to_ggp = travel_times[(current_location, 'Golden Gate Park')]
    arrive_ggp = current_time + timedelta(minutes=travel_to_ggp)
    barbara_meet_start = max(arrive_ggp, barbara_available_start)
    barbara_meet_end = barbara_meet_start + barbara_min_duration
    
    if barbara_meet_end <= barbara_available_end:
        itinerary.append({
            "action": "meet",
            "location": "Golden Gate Park",
            "person": "Barbara",
            "start_time": format_time(barbara_meet_start),
            "end_time": format_time(barbara_meet_end)
        })
        return {"itinerary": itinerary}
    
    # If no meetings possible
    return {"itinerary": []}

if __name__ == "__main__":
    schedule = calculate_schedule()
    print(json.dumps(schedule, indent=2))