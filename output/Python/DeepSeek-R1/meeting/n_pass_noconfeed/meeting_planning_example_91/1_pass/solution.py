import json

def time_to_minutes(time_str):
    parts = time_str.split(':')
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02}"

def main():
    start_time_str = "9:00"
    start_location = "Russian Hill"
    
    daniel_person = "Daniel"
    daniel_location = "Richmond District"
    daniel_available_start_str = "19:00"
    daniel_available_end_str = "20:15"
    min_duration = 75
    
    travel_time_to_richmond = 14
    
    start_minutes = time_to_minutes(start_time_str)
    daniel_start_minutes = time_to_minutes(daniel_available_start_str)
    daniel_end_minutes = time_to_minutes(daniel_available_end_str)
    
    departure_time = daniel_start_minutes - travel_time_to_richmond
    
    meeting = {
        "action": "meet",
        "location": daniel_location,
        "person": daniel_person,
        "start_time": daniel_available_start_str,
        "end_time": daniel_available_end_str
    }
    
    result = {
        "itinerary": [meeting]
    }
    
    print(json.dumps(result))

if __name__ == "__main__":
    main()