import json

def format_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    travel_times = {
        "Bayview": {
            "Embarcadero": 19,
            "Richmond District": 25,
            "Fisherman's Wharf": 25
        },
        "Embarcadero": {
            "Bayview": 21,
            "Richmond District": 21,
            "Fisherman's Wharf": 6
        },
        "Richmond District": {
            "Bayview": 26,
            "Embarcadero": 19,
            "Fisherman's Wharf": 18
        },
        "Fisherman's Wharf": {
            "Bayview": 26,
            "Embarcadero": 8,
            "Richmond District": 18
        }
    }
    
    start_time_minutes = 9 * 60
    
    jason_location = "Fisherman's Wharf"
    jason_start = 16 * 60
    jason_end = 16 * 60 + 45
    jason_min_duration = 30
    
    jessica_location = "Embarcadero"
    jessica_start = 16 * 60 + 45
    jessica_end = 19 * 60
    jessica_min_duration = 30
    
    sandra_location = "Richmond District"
    sandra_start = 18 * 60 + 30
    sandra_end = 21 * 60 + 45
    sandra_min_duration = 120
    
    travel_to_jason = travel_times["Bayview"][jason_location]
    leave_bayview = jason_start - travel_to_jason
    arrival_jason = jason_start
    
    travel_to_jessica = travel_times[jason_location][jessica_location]
    leave_jason = jessica_start - travel_to_jessica
    jason_meeting_duration = leave_jason - arrival_jason
    arrival_jessica = jessica_start
    
    travel_to_sandra = travel_times[jessica_location][sandra_location]
    leave_jessica = sandra_start - travel_to_sandra
    jessica_meeting_duration = leave_jessica - arrival_jessica
    arrival_sandra = sandra_start
    
    sandra_meeting_end = arrival_sandra + sandra_min_duration
    
    itinerary = [
        {
            "action": "meet",
            "location": jason_location,
            "person": "Jason",
            "start_time": format_time(arrival_jason),
            "end_time": format_time(leave_jason)
        },
        {
            "action": "meet",
            "location": jessica_location,
            "person": "Jessica",
            "start_time": format_time(arrival_jessica),
            "end_time": format_time(leave_jessica)
        },
        {
            "action": "meet",
            "location": sandra_location,
            "person": "Sandra",
            "start_time": format_time(arrival_sandra),
            "end_time": format_time(sandra_meeting_end)
        }
    ]
    
    result = {
        "itinerary": itinerary
    }
    print(json.dumps(result))

if __name__ == "__main__":
    main()