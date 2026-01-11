import json
from datetime import datetime, timedelta

def calculate_end_time(start_time, duration_minutes):
    return start_time + timedelta(minutes=duration_minutes)

def is_valid_meeting_slot(available_start, available_end, meeting_start, meeting_duration):
    meeting_end = calculate_end_time(meeting_start, meeting_duration)
    return meeting_start >= available_start and meeting_end <= available_end

def find_optimal_schedule():
    # Define start time and travel times
    start_time = datetime.strptime("9:00", "%H:%M")
    travel_times = {
        ("Bayview", "Union Square"): 17,
        ("Bayview", "Presidio"): 31,
        ("Union Square", "Bayview"): 15,
        ("Union Square", "Presidio"): 24,
        ("Presidio", "Bayview"): 31,
        ("Presidio", "Union Square"): 22
    }
    
    # Define availability and required meeting durations
    richard_availability = (datetime.strptime("8:45", "%H:%M"), datetime.strptime("13:00", "%H:%M"))
    charles_availability = (datetime.strptime("9:45", "%H:%M"), datetime.strptime("13:00", "%H:%M"))
    meeting_duration = 120
    
    # Initialize variables to store the best schedule
    best_schedule = None
    best_total_time = float('inf')
    
    # Try all possible orders of meeting Richard and Charles
    for first_meeting, second_meeting in [("Richard", "Charles"), ("Charles", "Richard")]:
        if first_meeting == "Richard":
            first_location = "Union Square"
            second_location = "Presidio"
            first_availability = richard_availability
            second_availability = charles_availability
        else:
            first_location = "Presidio"
            second_location = "Union Square"
            first_availability = charles_availability
            second_availability = richard_availability
        
        # Calculate the earliest possible start time for the first meeting
        first_meeting_start = max(start_time + timedelta(minutes=travel_times[("Bayview", first_location)]), first_availability[0])
        
        # Check if the first meeting fits within the available time
        if is_valid_meeting_slot(first_availability[0], first_availability[1], first_meeting_start, meeting_duration):
            first_meeting_end = calculate_end_time(first_meeting_start, meeting_duration)
            
            # Calculate the earliest possible start time for the second meeting
            second_meeting_start = first_meeting_end + timedelta(minutes=travel_times[(first_location, second_location)])
            
            # Check if the second meeting fits within the available time
            if is_valid_meeting_slot(second_availability[0], second_availability[1], second_meeting_start, meeting_duration):
                second_meeting_end = calculate_end_time(second_meeting_start, meeting_duration)
                
                # Calculate the total time spent
                total_time = (second_meeting_end - start_time).total_seconds() / 60
                
                # Update the best schedule if this one is better
                if total_time < best_total_time:
                    best_total_time = total_time
                    best_schedule = [
                        {"action": "meet", "location": first_location, "person": first_meeting, 
                         "start_time": first_meeting_start.strftime("%H:%M").lstrip('0'), 
                         "end_time": first_meeting_end.strftime("%H:%M").lstrip('0')},
                        {"action": "meet", "location": second_location, "person": second_meeting, 
                         "start_time": second_meeting_start.strftime("%H:%M").lstrip('0'), 
                         "end_time": second_meeting_end.strftime("%H:%M").lstrip('0')}
                    ]
    
    # Return the best schedule as JSON
    return json.dumps({"itinerary": best_schedule}, indent=2)

# Output the optimal schedule
print(find_optimal_schedule())