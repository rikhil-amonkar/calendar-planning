import json

def calculate_optimal_schedule():
    # Input parameters
    arrival_time = "9:00"
    arrival_location = "Alamo Square"
    
    # Timothy's availability
    timothy_location = "Richmond District"
    timothy_start = "20:45"
    timothy_end = "21:30"
    min_meeting_duration = 45  # minutes
    
    # Travel times
    travel_to_richmond = 12  # minutes from Alamo Square to Richmond District
    travel_back = 13  # minutes from Richmond District to Alamo Square
    
    # Parse times into minutes since midnight
    def parse_time(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm
    
    arrival_min = parse_time(arrival_time)
    timothy_start_min = parse_time(timothy_start)
    timothy_end_min = parse_time(timothy_end)
    
    # Calculate latest possible departure time to meet Timothy
    latest_departure = timothy_end_min - min_meeting_duration
    if latest_departure < timothy_start_min:
        latest_departure = timothy_start_min
    
    # Calculate latest possible start time to travel to Richmond
    latest_travel_start = latest_departure - travel_to_richmond
    
    # Check if we can make it to Richmond in time
    if arrival_min <= latest_travel_start:
        # We can meet Timothy
        meet_start = max(timothy_start_min, arrival_min + travel_to_richmond)
        meet_end = meet_start + min_meeting_duration
        if meet_end > timothy_end_min:
            meet_end = timothy_end_min
        
        itinerary = [
            {
                "action": "travel",
                "location": "Richmond District",
                "person": "N/A",
                "start_time": f"{arrival_min // 60}:{arrival_min % 60:02d}",
                "end_time": f"{(arrival_min + travel_to_richmond) // 60}:{(arrival_min + travel_to_richmond) % 60:02d}"
            },
            {
                "action": "meet",
                "location": "Richmond District",
                "person": "Timothy",
                "start_time": f"{meet_start // 60}:{meet_start % 60:02d}",
                "end_time": f"{meet_end // 60}:{meet_end % 60:02d}"
            },
            {
                "action": "travel",
                "location": "Alamo Square",
                "person": "N/A",
                "start_time": f"{meet_end // 60}:{meet_end % 60:02d}",
                "end_time": f"{(meet_end + travel_back) // 60}:{(meet_end + travel_back) % 60:02d}"
            }
        ]
    else:
        # Cannot meet Timothy
        itinerary = [
            {
                "action": "stay",
                "location": "Alamo Square",
                "person": "N/A",
                "start_time": f"{arrival_min // 60}:{arrival_min % 60:02d}",
                "end_time": f"{arrival_min // 60}:{arrival_min % 60:02d}"
            }
        ]
    
    result = {
        "itinerary": itinerary
    }
    
    return json.dumps(result, indent=2)

print(calculate_optimal_schedule())