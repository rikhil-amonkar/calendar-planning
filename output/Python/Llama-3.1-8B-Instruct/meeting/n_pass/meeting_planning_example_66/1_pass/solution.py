import json
from datetime import datetime, timedelta

def calculate_travel_time(distance, start_time):
    # Assuming travel time is equal to distance
    travel_time = timedelta(minutes=distance)
    end_time = start_time + travel_time
    return end_time

def compute_optimal_schedule(arrival_time, constraints):
    optimal_schedule = []
    nob_hill = "Nob Hill"
    presidio = "Presidio"
    
    # Meeting Robert at Presidio from 11:15AM to 5:45PM
    start_time = datetime.strptime("11:15", "%H:%M")
    end_time = datetime.strptime("5:45", "%H:%M")
    
    if start_time < arrival_time + timedelta(hours=1):  # Ensure we arrive before Robert starts
        # Calculate earliest meeting time
        earliest_meeting_time = max(start_time, arrival_time + timedelta(minutes=17))
        
        # Check if meeting Robert for 120 minutes is possible
        if end_time - earliest_meeting_time >= timedelta(minutes=120):
            # Add meeting to schedule
            optimal_schedule.append({
                "action": "meet",
                "location": presidio,
                "person": "Robert",
                "start_time": earliest_meeting_time.strftime("%H:%M"),
                "end_time": (earliest_meeting_time + timedelta(minutes=120)).strftime("%H:%M")
            })
    
    return optimal_schedule

def main():
    arrival_time = datetime.strptime("09:00", "%H:%M")
    nob_hill_to_presidio = 17
    presidio_to_nob_hill = 18
    robert_start_time = datetime.strptime("11:15", "%H:%M")
    robert_end_time = datetime.strptime("5:45", "%H:%M")
    min_meeting_duration = 120
    
    # Calculate optimal schedule
    optimal_schedule = compute_optimal_schedule(arrival_time, {
        "robert_start_time": robert_start_time,
        "robert_end_time": robert_end_time,
        "min_meeting_duration": min_meeting_duration
    })
    
    # Add travel to schedule
    if optimal_schedule:
        optimal_schedule[0]["start_time"] = (arrival_time + timedelta(minutes=17)).strftime("%H:%M")
        optimal_schedule[0]["action"] = "travel"
        optimal_schedule[0]["location"] = "Presidio"
        optimal_schedule[0]["person"] = "None"
        
        optimal_schedule.append({
            "action": "travel",
            "location": "Nob Hill",
            "person": "None",
            "start_time": (robert_end_time + timedelta(minutes=18)).strftime("%H:%M"),
            "end_time": (robert_end_time + timedelta(minutes=18)).strftime("%H:%M")
        })
    
    # Output schedule as JSON
    print(json.dumps({"itinerary": optimal_schedule}, indent=4))

if __name__ == "__main__":
    main()