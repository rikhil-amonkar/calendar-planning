import json
from datetime import datetime, timedelta

def compute_schedule(arrival_time, travel_time, start_time_stephanie, end_time_stephanie, min_meeting_duration):
    schedule = []
    
    # Start at Marina District
    schedule.append({"action": "start", "location": "Marina District", "time": arrival_time.strftime("%I:%M%p")})
    
    # Travel to Mission District
    travel_time_minutes = travel_time * 60
    departure_time = datetime.strptime(arrival_time.strftime("%I:%M%p"), "%I:%M%p")
    departure_time += timedelta(minutes=travel_time_minutes)
    schedule.append({"action": "travel", "location": "Marina District", "duration": travel_time_minutes, "time": departure_time.strftime("%I:%M%p"), "to": "Mission District"})
    
    # Wait for Stephanie to arrive
    wait_time = start_time_stephanie - departure_time
    schedule.append({"action": "wait", "location": "Mission District", "time": (departure_time + wait_time).strftime("%I:%M%p")})
    
    # Meet Stephanie
    meeting_start_time = (departure_time + wait_time).strftime("%I:%M%p")
    meeting_duration = max(0, min_meeting_duration - (end_time_stephanie - (departure_time + wait_time)).total_seconds() / 60)
    schedule.append({"action": "meet", "location": "Mission District", "duration": meeting_duration, "time": (departure_time + wait_time + timedelta(minutes=meeting_duration)).strftime("%I:%M%p")})
    
    return schedule

def main():
    arrival_time = datetime.strptime("9:00AM", "%I:%M%p")
    travel_time = 20 / 60  # convert minutes to hours
    start_time_stephanie = datetime.strptime("10:30AM", "%I:%M%p")
    end_time_stephanie = datetime.strptime("1:30PM", "%I:%M%p")
    min_meeting_duration = 120
    
    schedule = compute_schedule(arrival_time, travel_time, start_time_stephanie, end_time_stephanie, min_meeting_duration)
    
    print(json.dumps({"schedule": schedule}, indent=4))

if __name__ == "__main__":
    main()