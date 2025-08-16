import json
from datetime import datetime, timedelta

# Define the travel times
travel_times = {
    "The Castro": {"Richmond District": 16, "Haight-Ashbury": 6, "Pacific Heights": 16},
    "Richmond District": {"The Castro": 16, "Haight-Ashbury": 10, "Pacific Heights": 10},
    "Haight-Ashbury": {"The Castro": 6, "Richmond District": 10, "Pacific Heights": 12},
    "Pacific Heights": {"The Castro": 16, "Richmond District": 10, "Haight-Ashbury": 12},
    "Financial District": {"Marina District": 15, "Joseph": 15},
    "Marina District": {"Financial District": 15, "Karen": 15},
    "Joseph": {"Financial District": 15},
    "Karen": {"Marina District": 15},
    "Anthony": {"Haight-Ashbury": 0},  # No travel needed as it's the starting point
    "Helen": {"Pacific Heights": 0},  # No travel needed as it's the starting point
    "Joshua": {"Richmond District": 0}  # No travel needed as it's the starting point
}

# Define the meeting constraints
meetings = {
    "Joshua": {"location": "Richmond District", "start": "09:00", "end": "20:00", "min_duration": 15},
    "Anthony": {"location": "Haight-Ashbury", "start": "07:15", "end": "10:30", "min_duration": 30},
    "Helen": {"location": "Pacific Heights", "start": "08:00", "end": "12:00", "min_duration": 75},
    "Joseph": {"location": "Financial District", "start": "11:15", "end": "13:30", "min_duration": 15},
    "Karen": {"location": "Marina District", "start": "11:30", "end": "18:30", "min_duration": 15}
}

# Convert times to datetime objects
def convert_to_datetime(time_str, base_date):
    return datetime.strptime(f"{base_date} {time_str}", "%Y-%m-%d %H:%M")

# Generate all possible schedules
def generate_schedules(meetings, base_date):
    def backtrack(current_schedule, current_location, current_time):
        if len(current_schedule) == len(meetings):
            schedules.append(current_schedule.copy())
            return
        
        for person, details in meetings.items():
            if person not in seen:
                location = details["location"]
                start_time = convert_to_datetime(details["start"], base_date)
                end_time = convert_to_datetime(details["end"], base_date)
                min_duration = timedelta(minutes=details["min_duration"])
                
                travel_time = timedelta(minutes=travel_times.get(current_location, {}).get(location, 0))
                potential_start_time = current_time + travel_time
                
                if potential_start_time + min_duration <= end_time:
                    seen.add(person)
                    current_schedule.append({"action": "travel", "location": location})
                    current_schedule.append({"action": "meet", "location": location, "person": person, "start_time": potential_start_time.strftime("%H:%M"), "end_time": (potential_start_time + min_duration).strftime("%H:%M")})
                    backtrack(current_schedule, location, potential_start_time + min_duration)
                    current_schedule.pop()
                    current_schedule.pop()
                    seen.remove(person)
    
    schedules = []
    seen = set()
    backtrack([], "The Castro", convert_to_datetime("09:00", base_date))
    return schedules

# Find the optimal schedule
def find_optimal_schedule(schedules, base_date):
    optimal_schedule = None
    max_meeting_time = timedelta()
    
    for schedule in schedules:
        total_meeting_time = timedelta()
        last_location = "The Castro"
        current_time = convert_to_datetime("09:00", base_date)
        
        valid_schedule = True
        for item in schedule:
            if item["action"] == "travel":
                travel_time = timedelta(minutes=travel_times[last_location][item["location"]])
                current_time += travel_time
            
            if item["action"] == "meet":
                start_time = convert_to_datetime(item["start_time"], base_date)
                end_time = convert_to_datetime(item["end_time"], base_date)
                duration = end_time - start_time
                total_meeting_time += duration
                current_time = end_time
                
                # Check if the meeting time is within the person's availability
                person = item["person"]
                meeting_start = convert_to_datetime(meetings[person]["start"], base_date)
                meeting_end = convert_to_datetime(meetings[person]["end"], base_date)
                if not (meeting_start <= start_time < end_time <= meeting_end):
                    valid_schedule = False
                    break
            
            last_location = item["location"]
        
        if valid_schedule and total_meeting_time > max_meeting_time:
            max_meeting_time = total_meeting_time
            optimal_schedule = schedule
    
    return optimal_schedule

# Main function
def main():
    base_date = "2023-10-01"
    schedules = generate_schedules(meetings, base_date)
    optimal_schedule = find_optimal_schedule(schedules, base_date)
    
    # Convert the optimal schedule to the required JSON format
    result = {"itinerary": []}
    if optimal_schedule:
        for item in optimal_schedule:
            if item["action"] == "meet":
                result["itinerary"].append({
                    "action": "meet",
                    "location": item["location"],
                    "person": item["person"],
                    "start_time": item["start_time"],
                    "end_time": item["end_time"]
                })
    
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()