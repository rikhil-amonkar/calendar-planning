import json
from datetime import datetime, timedelta

# Constants
TRAVEL_TIME_ALAMO_TO_RICHMOND = 12  # in minutes
TRAVEL_TIME_RICHMOND_TO_ALAMO = 13  # in minutes
MEETING_DURATION_MINUTES = 45
ARRIVAL_TIME_ALAMO = datetime.strptime("09:00", "%H:%M")

# Timothy's availability
timothy_start = datetime.strptime("20:45", "%H:%M")
timothy_end = datetime.strptime("21:30", "%H:%M")

# Calculate the optimal meeting time considering travel and meeting constraints
def find_optimal_meeting_time():
    # The latest start time for the meeting with Timothy considering travel and meeting duration
    latest_meeting_start_time = timothy_end - timedelta(minutes=MEETING_DURATION_MINUTES)
    
    # Travel from Alamo Square to Richmond District
    travel_to_timothy = ARRIVAL_TIME_ALAMO + timedelta(minutes=TRAVEL_TIME_ALAMO_TO_RICHMOND)
    
    # Check if we can meet Timothy
    if travel_to_timothy <= latest_meeting_start_time:
        meeting_start_time = max(travel_to_timothy, timothy_start)
        meeting_end_time = meeting_start_time + timedelta(minutes=MEETING_DURATION_MINUTES)
        
        return [{
            "action": "meet",
            "location": "Richmond District",
            "person": "Timothy",
            "start_time": meeting_start_time.strftime("%H:%M"),
            "end_time": meeting_end_time.strftime("%H:%M"),
        }]
    
    return []

# Main execution
def main():
    itinerary = find_optimal_meeting_time()
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

# Run the program
if __name__ == "__main__":
    main()