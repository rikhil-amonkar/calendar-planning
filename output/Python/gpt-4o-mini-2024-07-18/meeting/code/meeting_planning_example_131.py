import json
from datetime import datetime, timedelta

def calculate_schedule():
    # Define travel time (in minutes) between locations
    travel_times = {
        ("Pacific Heights", "Presidio"): 11,
        ("Pacific Heights", "Marina District"): 6,
        ("Presidio", "Pacific Heights"): 11,
        ("Presidio", "Marina District"): 10,
        ("Marina District", "Pacific Heights"): 7,
        ("Marina District", "Presidio"): 10,
    }
    
    # Define meeting constraints
    arrival_time_pacific = datetime.strptime("09:00", "%H:%M")
    meeting_window_jason_start = datetime.strptime("10:00", "%H:%M")
    meeting_window_jason_end = datetime.strptime("16:15", "%H:%M")
    meeting_duration_jason = timedelta(minutes=90)
    
    meeting_window_kenneth_start = datetime.strptime("15:30", "%H:%M")
    meeting_window_kenneth_end = datetime.strptime("16:45", "%H:%M")
    meeting_duration_kenneth = timedelta(minutes=45)
    
    schedule = []
    
    # Try to meet Jason first
    # Arrive at Presidio first to meet Jason
    travel_to_presidio = travel_times[("Pacific Heights", "Presidio")]
    jason_start_time = max(arrival_time_pacific + timedelta(minutes=travel_to_presidio), meeting_window_jason_start)
    jason_end_time = jason_start_time + meeting_duration_jason
    
    if jason_end_time <= meeting_window_jason_end:
        schedule.append({
            "action": "meet",
            "location": "Presidio",
            "person": "Jason",
            "start_time": jason_start_time.strftime("%H:%M"),
            "end_time": jason_end_time.strftime("%H:%M"),
        })
        
        # Move to Marina District to meet Kenneth
        travel_to_marina = travel_times[("Presidio", "Marina District")]
        travel_time_after_jason = travel_to_marina

        kenneth_start_time = max(jason_end_time + timedelta(minutes=travel_time_after_jason), meeting_window_kenneth_start)
        kenneth_end_time = kenneth_start_time + meeting_duration_kenneth
        
        if kenneth_end_time <= meeting_window_kenneth_end:
            schedule.append({
                "action": "meet",
                "location": "Marina District",
                "person": "Kenneth",
                "start_time": kenneth_start_time.strftime("%H:%M"),
                "end_time": kenneth_end_time.strftime("%H:%M"),
            })
        else:
            # If unable to meet Kenneth after Jason, it's best to try meeting Kenneth first
            # Try to meet Kenneth before Jason
            travel_to_marina = travel_times[("Pacific Heights", "Marina District")]
            kenneth_start_time = max(arrival_time_pacific + timedelta(minutes=travel_to_marina), meeting_window_kenneth_start)
            kenneth_end_time = kenneth_start_time + meeting_duration_kenneth
            
            if kenneth_end_time <= meeting_window_kenneth_end:
                schedule.append({
                    "action": "meet",
                    "location": "Marina District",
                    "person": "Kenneth",
                    "start_time": kenneth_start_time.strftime("%H:%M"),
                    "end_time": kenneth_end_time.strftime("%H:%M"),
                })
                
                # Move to Presidio to meet Jason
                travel_to_presidio = travel_times[("Marina District", "Presidio")]
                jason_start_time = max(kenneth_end_time + timedelta(minutes=travel_to_presidio), meeting_window_jason_start)
                jason_end_time = jason_start_time + meeting_duration_jason
                
                if jason_end_time <= meeting_window_jason_end:
                    schedule.append({
                        "action": "meet",
                        "location": "Presidio",
                        "person": "Jason",
                        "start_time": jason_start_time.strftime("%H:%M"),
                        "end_time": jason_end_time.strftime("%H:%M"),
                    })
                    
    return json.dumps({"itinerary": schedule}, indent=2)

if __name__ == "__main__":
    print("SOLUTION:")
    print(calculate_schedule())