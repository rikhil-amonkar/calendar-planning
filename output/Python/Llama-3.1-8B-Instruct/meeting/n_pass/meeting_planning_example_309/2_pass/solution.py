import json
from datetime import datetime, timedelta

def calculate_travel_time(origin, destination, travel_times):
    return travel_times[f"{origin}-{destination}"]

def calculate_meeting_time(start_time, duration):
    # Convert start_time to a datetime object
    start_time = datetime.strptime(start_time, "%H:%M")
    
    # Calculate the end time by adding the duration to the start time
    end_time = start_time + timedelta(minutes=duration)
    
    # Convert the end time back to a string in the format "%H:%M"
    end_time = end_time.strftime("%H:%M")
    
    return end_time

def compute_optimal_schedule(arrival_time, nancy_constraints, mary_constraints, jessica_constraints, rebecca_constraints, travel_times):
    schedule = []
    current_time = datetime.strptime(arrival_time, "%H:%M")
    
    # Meet Rebecca
    if current_time < datetime.strptime("07:00", "%H:%M"):
        current_time = datetime.strptime("07:00", "%H:%M")
    schedule.append({
        "action": "meet",
        "location": "Fisherman's Wharf",
        "person": "Rebecca",
        "start_time": current_time.strftime("%H:%M"),
        "end_time": calculate_meeting_time(current_time.strftime("%H:%M"), 45)
    })
    current_time = datetime.strptime(calculate_meeting_time(current_time.strftime("%H:%M"), 45), "%H:%M")
    travel_time = calculate_travel_time("Fisherman's Wharf", "Financial District", travel_times)
    current_time += timedelta(minutes=travel_time)
    
    # Meet Nancy
    if current_time < datetime.strptime("09:30", "%H:%M"):
        current_time = datetime.strptime("09:30", "%H:%M")
    schedule.append({
        "action": "meet",
        "location": "Chinatown",
        "person": "Nancy",
        "start_time": current_time.strftime("%H:%M"),
        "end_time": calculate_meeting_time(current_time.strftime("%H:%M"), 90)
    })
    current_time = datetime.strptime(calculate_meeting_time(current_time.strftime("%H:%M"), 90), "%H:%M")
    travel_time = calculate_travel_time("Chinatown", "Alamo Square", travel_times)
    current_time += timedelta(minutes=travel_time)
    
    # Meet Mary
    if current_time < datetime.strptime("07:00", "%H:%M"):
        current_time = datetime.strptime("07:00", "%H:%M")
    schedule.append({
        "action": "meet",
        "location": "Alamo Square",
        "person": "Mary",
        "start_time": current_time.strftime("%H:%M"),
        "end_time": calculate_meeting_time(current_time.strftime("%H:%M"), 75)
    })
    current_time = datetime.strptime(calculate_meeting_time(current_time.strftime("%H:%M"), 75), "%H:%M")
    travel_time = calculate_travel_time("Alamo Square", "Bayview", travel_times)
    current_time += timedelta(minutes=travel_time)
    
    # Meet Jessica
    if current_time < datetime.strptime("11:15", "%H:%M"):
        current_time = datetime.strptime("11:15", "%H:%M")
    schedule.append({
        "action": "meet",
        "location": "Bayview",
        "person": "Jessica",
        "start_time": current_time.strftime("%H:%M"),
        "end_time": calculate_meeting_time(current_time.strftime("%H:%M"), 45)
    })
    current_time = datetime.strptime(calculate_meeting_time(current_time.strftime("%H:%M"), 45), "%H:%M")
    
    return schedule

def main():
    travel_times = {
        "Financial District-Chinatown": 5,
        "Financial District-Alamo Square": 17,
        "Financial District-Bayview": 19,
        "Financial District-Fisherman's Wharf": 10,
        "Chinatown-Financial District": 5,
        "Chinatown-Alamo Square": 17,
        "Chinatown-Bayview": 22,
        "Chinatown-Fisherman's Wharf": 8,
        "Alamo Square-Financial District": 17,
        "Alamo Square-Chinatown": 16,
        "Alamo Square-Bayview": 16,
        "Alamo Square-Fisherman's Wharf": 19,
        "Bayview-Financial District": 19,
        "Bayview-Chinatown": 18,
        "Bayview-Alamo Square": 16,
        "Bayview-Fisherman's Wharf": 25,
        "Fisherman's Wharf-Financial District": 11,
        "Fisherman's Wharf-Chinatown": 12,
        "Fisherman's Wharf-Alamo Square": 20,
        "Fisherman's Wharf-Bayview": 26
    }
    
    nancy_constraints = {"start_time": "09:30", "end_time": "13:30"}
    mary_constraints = {"start_time": "07:00", "end_time": "21:00"}
    jessica_constraints = {"start_time": "11:15", "end_time": "14:45"}
    rebecca_constraints = {"start_time": "07:00", "end_time": "08:30"}
    arrival_time = "09:00"
    
    optimal_schedule = compute_optimal_schedule(arrival_time, nancy_constraints, mary_constraints, jessica_constraints, rebecca_constraints, travel_times)
    
    print(json.dumps({"itinerary": optimal_schedule}, indent=4))

if __name__ == "__main__":
    main()