import json
from datetime import datetime, timedelta

# Define the travel times
travel_times = {
    "The Castro": {"Alamo Square": 8, "Richmond District": 16, "Financial District": 21, "Union Square": 19, "Fisherman's Wharf": 24, "Marina District": 21, "Haight-Ashbury": 6, "Mission District": 7, "Pacific Heights": 16, "Golden Gate Park": 11},
    "Alamo Square": {"The Castro": 8, "Richmond District": 11, "Financial District": 17, "Union Square": 14, "Fisherman's Wharf": 19, "Marina District": 15, "Haight-Ashbury": 5, "Mission District": 10, "Pacific Heights": 10, "Golden Gate Park": 9},
    "Richmond District": {"The Castro": 16, "Alamo Square": 11, "Financial District": 22, "Union Square": 21, "Fisherman's Wharf": 18, "Marina District": 9, "Haight-Ashbury": 10, "Mission District": 20, "Pacific Heights": 10, "Golden Gate Park": 9},
    "Financial District": {"The Castro": 20, "Alamo Square": 17, "Richmond District": 21, "Union Square": 9, "Fisherman's Wharf": 10, "Marina District": 15, "Haight-Ashbury": 19, "Mission District": 17, "Pacific Heights": 13, "Golden Gate Park": 23},
    "Union Square": {"The Castro": 17, "Alamo Square": 15, "Richmond District": 20, "Financial District": 9, "Fisherman's Wharf": 15, "Marina District": 18, "Haight-Ashbury": 18, "Mission District": 14, "Pacific Heights": 15, "Golden Gate Park": 22},
    "Fisherman's Wharf": {"The Castro": 27, "Alamo Square": 21, "Richmond District": 18, "Financial District": 11, "Union Square": 13, "Marina District": 10, "Haight-Ashbury": 23, "Mission District": 22, "Pacific Heights": 13, "Golden Gate Park": 25},
    "Marina District": {"The Castro": 22, "Alamo Square": 15, "Richmond District": 11, "Financial District": 17, "Union Square": 16, "Fisherman's Wharf": 10, "Haight-Ashbury": 17, "Mission District": 19, "Pacific Heights": 7, "Golden Gate Park": 18},
    "Haight-Ashbury": {"The Castro": 6, "Alamo Square": 5, "Richmond District": 10, "Financial District": 21, "Union Square": 19, "Fisherman's Wharf": 23, "Marina District": 17, "Mission District": 12, "Pacific Heights": 12, "Golden Gate Park": 7},
    "Mission District": {"The Castro": 7, "Alamo Square": 11, "Richmond District": 20, "Financial District": 15, "Union Square": 15, "Fisherman's Wharf": 22, "Marina District": 19, "Haight-Ashbury": 12, "Pacific Heights": 16, "Golden Gate Park": 17},
    "Pacific Heights": {"The Castro": 16, "Alamo Square": 10, "Richmond District": 12, "Financial District": 13, "Union Square": 12, "Fisherman's Wharf": 13, "Marina District": 6, "Haight-Ashbury": 11, "Mission District": 15, "Golden Gate Park": 15},
    "Golden Gate Park": {"The Castro": 13, "Alamo Square": 9, "Richmond District": 7, "Financial District": 26, "Union Square": 22, "Fisherman's Wharf": 24, "Marina District": 16, "Haight-Ashbury": 7, "Mission District": 17, "Pacific Heights": 15}
}

# Define the meeting constraints
meetings = {
    "William": {"location": "Alamo Square", "start": "15:15", "end": "17:15", "min_duration": 60},
    "Joshua": {"location": "Richmond District", "start": "07:00", "end": "20:00", "min_duration": 15},
    "Joseph": {"location": "Financial District", "start": "11:15", "end": "13:30", "min_duration": 15},
    "David": {"location": "Union Square", "start": "16:45", "end": "19:15", "min_duration": 45},
    "Brian": {"location": "Fisherman's Wharf", "start": "13:45", "end": "20:45", "min_duration": 105},
    "Karen": {"location": "Marina District", "start": "11:30", "end": "18:30", "min_duration": 15},
    "Anthony": {"location": "Haight-Ashbury", "start": "07:15", "end": "10:30", "min_duration": 30},
    "Matthew": {"location": "Mission District", "start": "17:15", "end": "19:15", "min_duration": 120},
    "Helen": {"location": "Pacific Heights", "start": "08:00", "end": "12:00", "min_duration": 75},
    "Jeffrey": {"location": "Golden Gate Park", "start": "19:00", "end": "21:30", "min_duration": 60}
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
                
                travel_time = timedelta(minutes=travel_times[current_location][location])
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
    
    print(json.dumps(result))

if __name__ == "__main__":
    main()