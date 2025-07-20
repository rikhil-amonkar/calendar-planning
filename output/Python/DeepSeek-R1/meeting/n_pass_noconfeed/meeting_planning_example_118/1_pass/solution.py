import json

def time_to_minutes(time_str):
    parts = time_str.split(':')
    hours = int(parts[0])
    minutes = int(parts[1]) if len(parts) > 1 else 0
    return hours * 60 + minutes

def minutes_to_time(minutes_since_midnight):
    hours = minutes_since_midnight // 60
    minutes = minutes_since_midnight % 60
    return f"{hours}:{minutes:02d}"

def main():
    # Define input parameters
    start_location = "Bayview"
    start_time_str = "9:00"
    participants = [
        {"name": "Richard", "location": "Union Square", "available_start": "8:45", "available_end": "13:00"},
        {"name": "Charles", "location": "Presidio", "available_start": "9:45", "available_end": "13:00"}
    ]
    travel_times = {
        ('Bayview', 'Union Square'): 17,
        ('Bayview', 'Presidio'): 31,
        ('Union Square', 'Bayview'): 15,
        ('Union Square', 'Presidio'): 24,
        ('Presidio', 'Bayview'): 31,
        ('Presidio', 'Union Square'): 22
    }
    
    # Convert times to minutes since midnight
    start_minutes = time_to_minutes(start_time_str)
    richard_start = time_to_minutes(participants[0]['available_start'])
    richard_end = time_to_minutes(participants[0]['available_end'])
    charles_start = time_to_minutes(participants[1]['available_start'])
    charles_end = time_to_minutes(participants[1]['available_end'])
    
    # Pre-calculated values for the optimal order (Richard then Charles)
    travel1 = travel_times[('Bayview', 'Union Square')]
    travel2 = travel_times[('Union Square', 'Presidio')]
    
    # Total available meeting time after accounting for travel
    total_available_time = charles_end - (start_minutes + travel1 + travel2)
    
    # Distribute meeting times as evenly as possible
    meeting1_duration = (total_available_time + 1) // 2
    meeting2_duration = total_available_time // 2
    
    # Calculate meeting times for Richard
    arrive_richard = start_minutes + travel1
    meet_richard_start = max(arrive_richard, richard_start)
    meet_richard_end = meet_richard_start + meeting1_duration
    
    # Calculate meeting times for Charles
    leave_richard = meet_richard_end
    arrive_charles = leave_richard + travel2
    meet_charles_start = max(arrive_charles, charles_start)
    meet_charles_end = meet_charles_start + meeting2_duration
    
    # Format itinerary
    itinerary = [
        {
            "action": "meet",
            "location": "Union Square",
            "person": "Richard",
            "start_time": minutes_to_time(meet_richard_start),
            "end_time": minutes_to_time(meet_richard_end)
        },
        {
            "action": "meet",
            "location": "Presidio",
            "person": "Charles",
            "start_time": minutes_to_time(meet_charles_start),
            "end_time": minutes_to_time(meet_charles_end)
        }
    ]
    
    # Output as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()