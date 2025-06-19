import json

def main():
    travel_times = {
        'Sunset District': {'Chinatown': 30, 'Russian Hill': 24, 'North Beach': 29},
        'Chinatown': {'Sunset District': 29, 'Russian Hill': 7, 'North Beach': 3},
        'Russian Hill': {'Sunset District': 23, 'Chinatown': 9, 'North Beach': 5},
        'North Beach': {'Sunset District': 27, 'Chinatown': 6, 'Russian Hill': 4}
    }
    
    def format_time(minutes_from_900):
        total_minutes = 9 * 60 + minutes_from_900
        hours = total_minutes // 60
        minutes = total_minutes % 60
        return f"{hours}:{minutes:02d}"
    
    # Calculate times in minutes from 9:00 AM
    anthony_start = (13 * 60 + 15) - (9 * 60)  # 1:15 PM
    anthony_end = anthony_start + 60             # 2:15 PM
    
    rebecca_start = (19 * 60 + 30) - (9 * 60)   # 7:30 PM
    rebecca_end = rebecca_start + 105            # 9:15 PM
    
    # Melissa meeting calculations
    arrive_north_beach = travel_times['Sunset District']['North Beach']  # 29 min
    melissa_duration = 105  # minimum required duration
    leave_north_beach = arrive_north_beach + melissa_duration  # 134 min (11:14 AM)
    
    itinerary = [
        {
            "action": "meet",
            "location": "North Beach",
            "person": "Melissa",
            "start_time": format_time(arrive_north_beach),  # 9:29 AM
            "end_time": format_time(leave_north_beach)      # 11:14 AM
        },
        {
            "action": "meet",
            "location": "Chinatown",
            "person": "Anthony",
            "start_time": format_time(anthony_start),  # 1:15 PM
            "end_time": format_time(anthony_end)       # 2:15 PM
        },
        {
            "action": "meet",
            "location": "Russian Hill",
            "person": "Rebecca",
            "start_time": format_time(rebecca_start),  # 7:30 PM
            "end_time": format_time(rebecca_end)       # 9:15 PM
        }
    ]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == '__main__':
    main()